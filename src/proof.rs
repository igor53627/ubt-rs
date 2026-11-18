//! Merkle proof generation and verification for the UBT.
//!
//! Proofs allow verifying that a key-value pair exists in the tree
//! without having the full tree.

use alloy_primitives::B256;

use crate::{
    error::Result, merkle::MAX_DEPTH, Hasher, Stem, StemNode, SubIndex, TreeKey, UbtError, STEM_LEN,
};

/// Direction in the tree (for proof paths)
///
/// The verifier does not trust it: the direction of the internal node at depth
/// `d` must agree with bit `d` of the key stem (0 is `Left`, 1 is `Right`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Direction {
    /// The proven node is the left child; the sibling hash is the right input of the hash.
    Left,
    /// The proven node is the right child; the sibling hash is the left input of the hash.
    Right,
}

/// A node in a Merkle proof path.
///
/// The enum is non-exhaustive: a later proof format can add a kind of node, so a
/// `match` outside this crate needs a wildcard arm.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum ProofNode {
    /// Sibling hash at an internal node level
    Internal {
        /// Hash of the sibling subtree.
        sibling: B256,
        /// Side of the internal node on which the proven node is.
        direction: Direction,
    },
    /// The stem node of the key, with the sibling hashes of its 256-leaf subtree.
    Stem {
        /// Stem of the stem node. It must be equal to the stem of the key.
        stem: Stem,
        /// Sibling hashes for the 8-level subtree (from leaf to root)
        subtree_siblings: Vec<B256>,
    },
    /// Another stem node is in the tree at the position of the key, so the key is absent.
    ///
    /// The node carries one present leaf of that stem node, as a stem proof does.
    /// The verifier computes the stem node hash from the leaf, so the hash is bound
    /// to `stem`, and an internal node of the tree cannot pass as a stem node.
    Extension {
        /// Stem of the stem node that is in the tree at this position. It is not
        /// equal to the stem of the key, and it shares with it the bits that the
        /// internal nodes of the path consume.
        stem: Stem,
        /// Subindex of a present leaf of that stem node.
        subindex: SubIndex,
        /// Value of that leaf.
        value: B256,
        /// Sibling hashes of that leaf in the 8-level subtree (from leaf to root).
        subtree_siblings: Vec<B256>,
    },
}

/// A Merkle proof for one key of the UBT.
///
/// The path goes from the leaf to the root, and has one of three forms:
///
/// | First node | Then | Claim |
/// |---|---|---|
/// | [`ProofNode::Stem`] | internal nodes | The stem node of the key is in the tree. `value` is the leaf, or `None` for an absent subindex. |
/// | [`ProofNode::Extension`] | internal nodes | Another stem node is at the position of the key. `value` is `None`. |
/// | none | internal nodes | The position of the key is an empty subtree. `value` is `None`. |
///
/// The path has at most 248 internal nodes, one for each bit of the stem that the
/// tree consumes above the position. [`Proof::compute_root`] rejects every other
/// path, and binds the path to `key`: see its documentation.
///
/// # Stem nodes and internal nodes
///
/// The hash of a stem node, `hash(stem || 0x00 || subtree_root)`, and the hash of an
/// internal node, `hash(left || right)`, are the same function of 64 bytes, so a
/// hash does not say which kind of node it is. Three rules of the verifier keep a
/// prover from using one kind as the other:
///
/// - An extension node carries a present leaf of the other stem node. An internal
///   node `hash(left || right)` with a `left` that ends in `0x00` does not pass
///   as the stem node of `left[..31]` when `right` has no leaf 8 levels below it.
/// - The left input of an internal node is not `stem || 0x00` of the key. Such a
///   node is the stem node of the key, read as an internal node. For the zero
///   stem, `stem || 0x00` is also an empty left child, so only a node with two
///   empty children passes. The cost: no proof shows that the zero stem is
///   absent at an empty position of a tree that is not empty.
/// - No left input of a node, and no `stem || 0x00` of a stem node or extension
///   node that has a leaf, starts with 12 zero bytes, unless it is zero. This is
///   the form of `0^12 || address`, the start of the input of
///   [`get_binary_tree_key`](crate::get_binary_tree_key). The key derivation
///   always uses SHA-256. With [`Sha256Hasher`](crate::Sha256Hasher), the hash
///   of that input ends in `0x00` for 1 of 256 derived stems, and then
///   `stem || 0x00` is the hash of a known input. A path can read that input as
///   an internal node or, for an address that ends in `0x00`, as the stem node
///   of the stem `0^12 || address[..19]`. The rule applies with every hasher.
///
/// # Limits
///
/// The rules assume a collision-resistant [`Hasher`]. They do not make a proof
/// sound for every tree, because the verifier sees one path and not the stems of
/// the other nodes:
///
/// - A tree is not safe when it holds a stem `s` and a party knows a 32-byte or
///   64-byte input whose hash is `s || 0x00`. That party can then prove that a
///   present key is absent or that an absent key is present, also for keys of
///   other stems. A party that can insert arbitrary stems needs about 2^9 to
///   2^10 attempts of one stem node hash each.
/// - For stems from the key derivation, the third rule rejects the paths that
///   read the input of the derivation as a node. It has no effect for the zero
///   address, whose `0^12 || address` is zero. A proof for a derived key stays
///   unsound when a node of the tree has the form of a derivation input as its
///   hash input, for example the stem node of a derived stem that starts with
///   12 zero bytes. This needs about 2^96 hashes.
/// - A valid proof is rejected when `stem || 0x00` of its key is the left input
///   of a node on its path, or when a left input on its path starts with 12
///   zero bytes and is not zero (a probability of 2^-96 for each hash).
/// - A valid proof is rejected when the stem of its stem node or extension node
///   starts with 12 zero bytes and is not zero, and the node has a leaf. This
///   also rejects the proof that another key is absent at the position of such
///   a stem node. A derived stem has this form with a probability of 2^-96.
///   For a stem that a caller selects, the rejection is certain:
///   [`UnifiedBinaryTree::insert`](crate::UnifiedBinaryTree::insert) accepts
///   such a stem.
///
/// The cause of the limits is the hash of EIP-7864: its input has no tag for the
/// kind of node. EIP-8297, the later design of the binary tree, puts a tag first
/// in each hash input (`LEAF_TAG`, `BRANCH_TAG`), and its text states that no
/// leaf input and branch input can coincide. This crate keeps the hash of
/// EIP-7864, so that its root hashes agree with go-ethereum `trie/bintrie`. No
/// change of the verifier removes the limits with that hash, so they stay
/// ([issue #26](https://github.com/igor53627/ubt-rs/issues/26)).
///
/// The rules and the limits come from tests and from a search over small trees.
/// They are not proven.
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

fn invalid_proof(reason: impl Into<String>) -> UbtError {
    UbtError::InvalidProof(reason.into())
}

/// Hash of a stem node from its stem and the root of its 256-leaf subtree.
///
/// A zero subtree root means that no leaf is present. Such a stem node hashes to
/// zero, as in [`StemNode::hash`].
///
/// A stem that starts with 12 zero bytes and is not zero is invalid when the node
/// has a leaf. Its `stem || 0x00` has the form `0^12 || address` of the input of
/// the key derivation, and a path then reads that input as a stem node.
fn stem_node_hash<H: Hasher>(hasher: &H, stem: &Stem, subtree_root: &B256) -> Result<B256> {
    if subtree_root.is_zero() {
        return Ok(B256::ZERO);
    }
    if has_derivation_form(&stem_node_prefix(stem)) {
        return Err(invalid_proof(
            "stem of a stem node has the form of a key derivation input",
        ));
    }
    Ok(hasher.hash_stem_node(stem.as_bytes(), subtree_root))
}

/// The first 32 bytes of the hash input of a stem node: `stem || 0x00`.
fn stem_node_prefix(stem: &Stem) -> B256 {
    let mut prefix = B256::ZERO;
    prefix[..STEM_LEN].copy_from_slice(stem.as_bytes());
    prefix
}

/// Root of the 256-leaf subtree of a stem node, from the hash of one leaf and its
/// 8 sibling hashes. The siblings go from leaf to root, so level 0 uses the lowest
/// bit of the subindex.
fn subtree_root<H: Hasher>(
    hasher: &H,
    (subindex, leaf_hash): (SubIndex, B256),
    subtree_siblings: &[B256],
) -> Result<B256> {
    if subtree_siblings.len() != 8 {
        return Err(invalid_proof(format!(
            "stem subtree siblings length must be 8, got {}",
            subtree_siblings.len()
        )));
    }
    let mut current_hash = leaf_hash;
    for (level, sibling) in subtree_siblings.iter().enumerate() {
        let bit = (subindex >> level) & 1;
        current_hash = if bit == 0 {
            node_hash(hasher, &current_hash, sibling)?
        } else {
            node_hash(hasher, sibling, &current_hash)?
        };
    }
    Ok(current_hash)
}

/// Number of zero bytes at the start of the input of the key derivation,
/// `0^12 || address || key` (see [`get_binary_tree_key`](crate::get_binary_tree_key)).
const DERIVATION_PREFIX_ZEROS: usize = 12;

/// True if the first 32 bytes of a hash input start with 12 zero bytes and are
/// not all zero: the form `0^12 || address` of the input of the key derivation.
fn has_derivation_form(first_input: &B256) -> bool {
    !first_input.is_zero()
        && first_input
            .iter()
            .take(DERIVATION_PREFIX_ZEROS)
            .all(|&byte| byte == 0)
}

/// `hash_64(left, right)` for one node of a proof.
///
/// A `left` that starts with 12 zero bytes and is not zero is invalid. It has the
/// form `0^12 || address` of the input of the key derivation, and a hash has this
/// form with a probability of 2^-96. With such a `left`, a path reads
/// `stem || 0x00` of a derived stem as the hash of a node.
fn node_hash<H: Hasher>(hasher: &H, left: &B256, right: &B256) -> Result<B256> {
    if has_derivation_form(left) {
        return Err(invalid_proof(
            "left input of a node has the form of a key derivation input, not of a hash",
        ));
    }
    Ok(hasher.hash_64(left, right))
}

impl Proof {
    /// Create a new proof.
    pub fn new(key: TreeKey, value: Option<B256>, path: Vec<ProofNode>) -> Self {
        Self { key, value, path }
    }

    /// Verify this proof against an expected root hash.
    ///
    /// Returns `Ok(true)` if the computed root matches `expected_root`. The proof
    /// then shows that the tree with this root has `value` at `key`, or has no
    /// leaf at `key` for `None`, within the limits that [`Proof`] states.
    ///
    /// # Errors
    ///
    /// Returns [`UbtError::InvalidProof`] if [`Proof::compute_root`] rejects the proof.
    pub fn verify<H: Hasher>(&self, hasher: &H, expected_root: &B256) -> Result<bool> {
        let computed_root = self.compute_root(hasher)?;
        Ok(&computed_root == expected_root)
    }

    /// Compute the root hash from this proof.
    ///
    /// The leaf contributes `hash_32(value)` for `Some(value)`, also for
    /// `Some(B256::ZERO)`, and 32 zero bytes for `None`. A stem node with no
    /// present leaf contributes 32 zero bytes, as [`StemNode::hash`] does.
    ///
    /// # Errors
    ///
    /// Returns [`UbtError::InvalidProof`] if the proof does not have one of the
    /// forms of [`Proof`], or is not bound to `key`:
    ///
    /// - a stem or extension node is not the first node of the path, or the path
    ///   has more than 248 internal nodes;
    /// - a stem or extension node has not exactly 8 sibling hashes;
    /// - a stem node has another stem than the key;
    /// - an extension node comes with a value, has the stem of the key, or has a
    ///   stem that does not share the consumed bits with the stem of the key;
    /// - a value comes without a stem node;
    /// - the direction of an internal node disagrees with the bit of the key stem
    ///   at the depth of that node;
    /// - the left input of an internal node is `stem || 0x00` of the key and the
    ///   node is not empty, or a left input starts with 12 zero bytes and is not
    ///   zero (see "Stem nodes and internal nodes" in [`Proof`]);
    /// - a stem or extension node with a leaf has a stem that starts with 12 zero
    ///   bytes and is not zero.
    pub fn compute_root<H: Hasher>(&self, hasher: &H) -> Result<B256> {
        let (position_hash, internal) = match self.path.split_first() {
            Some((
                ProofNode::Stem {
                    stem,
                    subtree_siblings,
                },
                rest,
            )) => (self.stem_node_claim(hasher, stem, subtree_siblings)?, rest),
            Some((
                ProofNode::Extension {
                    stem,
                    subindex,
                    value,
                    subtree_siblings,
                },
                rest,
            )) => {
                let leaf = (*subindex, hasher.hash_32(value));
                let subtree_root = subtree_root(hasher, leaf, subtree_siblings)?;
                (
                    self.other_stem_claim(hasher, stem, &subtree_root, rest.len())?,
                    rest,
                )
            }
            _ => (self.empty_position_claim()?, self.path.as_slice()),
        };
        self.root_from_position(hasher, position_hash, internal)
    }

    /// Root hash from the hash at the position of the key and the internal nodes
    /// above it, ordered from leaf to root.
    fn root_from_position<H: Hasher>(
        &self,
        hasher: &H,
        position_hash: B256,
        internal: &[ProofNode],
    ) -> Result<B256> {
        if internal.len() > MAX_DEPTH {
            return Err(invalid_proof(format!(
                "path has {} internal nodes, the maximum is {MAX_DEPTH}",
                internal.len()
            )));
        }
        let key_stem_node_prefix = stem_node_prefix(&self.key.stem);

        let mut current_hash = position_hash;
        // The first internal node is the deepest one: it is at depth `internal.len() - 1`.
        for (node, depth) in internal.iter().zip((0..internal.len()).rev()) {
            let ProofNode::Internal { sibling, direction } = node else {
                return Err(invalid_proof(
                    "a stem or extension node must be the first node of the path",
                ));
            };
            let key_direction = if self.key.stem.bit_at(depth) {
                Direction::Right
            } else {
                Direction::Left
            };
            if *direction != key_direction {
                return Err(invalid_proof(format!(
                    "direction at depth {depth} disagrees with the key stem"
                )));
            }
            let (left, right) = match direction {
                Direction::Left => (&current_hash, sibling),
                Direction::Right => (sibling, &current_hash),
            };
            // `hash_64(stem || 0x00, subtree_root)` is the hash of the stem node of
            // the key. A node with this left input is that stem node, read as an
            // internal node: the path goes on into its 256-leaf subtree, or into
            // `stem || 0x00` as if it were a hash. For the zero stem the left
            // input is zero, the same as an empty left child, so only a node with
            // two empty children passes.
            let is_empty_node = left.is_zero() && right.is_zero();
            if *left == key_stem_node_prefix && !is_empty_node {
                return Err(invalid_proof(format!(
                    "left input at depth {depth} is the stem of the key, not a hash"
                )));
            }
            current_hash = node_hash(hasher, left, right)?;
        }

        Ok(current_hash)
    }

    /// Hash of the stem node of the key, from the leaf and its 8 sibling hashes.
    fn stem_node_claim<H: Hasher>(
        &self,
        hasher: &H,
        stem: &Stem,
        subtree_siblings: &[B256],
    ) -> Result<B256> {
        if stem != &self.key.stem {
            return Err(invalid_proof("stem node has another stem than the key"));
        }
        let leaf_hash = match &self.value {
            Some(value) => hasher.hash_32(value),
            None => B256::ZERO,
        };
        let subtree_root = subtree_root(hasher, (self.key.subindex, leaf_hash), subtree_siblings)?;
        stem_node_hash(hasher, stem, &subtree_root)
    }

    /// Hash of another stem node that is at the position of the key, `depth` bits
    /// below the root.
    fn other_stem_claim<H: Hasher>(
        &self,
        hasher: &H,
        stem: &Stem,
        subtree_root: &B256,
        depth: usize,
    ) -> Result<B256> {
        if self.value.is_some() {
            return Err(invalid_proof("extension node with a value"));
        }
        match stem.first_differing_bit(&self.key.stem) {
            None => Err(invalid_proof("extension node with the stem of the key")),
            Some(position) if position < depth => Err(invalid_proof(format!(
                "extension stem leaves the key path at bit {position}, above depth {depth}"
            ))),
            Some(_) => stem_node_hash(hasher, stem, subtree_root),
        }
    }

    /// Hash of the empty subtree at the position of the key.
    fn empty_position_claim(&self) -> Result<B256> {
        if self.value.is_some() {
            return Err(invalid_proof("a value needs a stem node as the first node"));
        }
        Ok(B256::ZERO)
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
                ProofNode::Extension {
                    subtree_siblings, ..
                } => STEM_LEN + 1 + 32 + subtree_siblings.len() * 32, // stem, subindex, value
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
/// For a stem node with no values, the value is `None` and the 8 siblings are zero.
/// [`Proof::compute_root`] gives `B256::ZERO` for such a proof, which is equal to
/// [`StemNode::hash`]. go-ethereum cannot have a stem node with no values.
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
        data[usize::from(idx)] = hasher.hash_32(&v);
    }

    // Collect siblings while building tree
    let mut siblings = Vec::with_capacity(8);
    let mut idx = usize::from(subindex);

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{get_basic_data_key, Address, Sha256Hasher, UnifiedBinaryTree};
    use std::collections::BTreeMap;

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
            ProofNode::Stem {
                stem: key.stem,
                subtree_siblings: vec![B256::ZERO; 8],
            },
            ProofNode::Internal {
                sibling: B256::ZERO,
                direction: Direction::Left,
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

    /// A stem node with no values hashes to zero for every stem. A proof from
    /// `generate_stem_proof` for such a node must reconstruct that hash, also for
    /// a stem that is not all zero. A stem node with one present zero leaf keeps
    /// the stem wrapper.
    #[test]
    fn test_proof_for_stem_node_with_no_values() {
        let hasher = Sha256Hasher;
        let stem = Stem::new([0x11u8; 31]);
        let proof_for = |node: &StemNode, subindex: u8| {
            let (value, siblings) = generate_stem_proof(node, subindex, &hasher);
            Proof::new(
                TreeKey::new(stem, subindex),
                value,
                vec![ProofNode::Stem {
                    stem,
                    subtree_siblings: siblings,
                }],
            )
        };

        let mut node = StemNode::new(stem);
        assert_eq!(node.hash(&hasher), B256::ZERO);
        for subindex in [0u8, 5, 255] {
            let proof = proof_for(&node, subindex);
            assert_eq!(proof.value, None);
            assert_eq!(proof.compute_root(&hasher).unwrap(), B256::ZERO);
            assert!(proof.verify(&hasher, &node.hash(&hasher)).unwrap());
        }

        node.set_value(3, B256::ZERO);
        let expected_root = node.hash(&hasher);
        assert_ne!(expected_root, B256::ZERO);
        let absent = proof_for(&node, 5);
        assert_eq!(absent.value, None);
        assert_eq!(absent.compute_root(&hasher).unwrap(), expected_root);
        let present = proof_for(&node, 3);
        assert_eq!(present.value, Some(B256::ZERO));
        assert_eq!(present.compute_root(&hasher).unwrap(), expected_root);
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

    // ---- Proofs for whole trees -------------------------------------------------

    /// A tree with its root from `UnifiedBinaryTree::root_hash` and its stem nodes
    /// sorted by stem.
    struct TestTree {
        tree: UnifiedBinaryTree<Sha256Hasher>,
        nodes: Vec<StemNode>,
        root: B256,
    }

    fn test_tree(entries: &[(TreeKey, B256)]) -> TestTree {
        let mut tree = UnifiedBinaryTree::<Sha256Hasher>::new();
        let mut by_stem: BTreeMap<Stem, StemNode> = BTreeMap::new();
        for (key, value) in entries {
            tree.insert(*key, *value);
            by_stem
                .entry(key.stem)
                .or_insert_with(|| StemNode::new(key.stem))
                .set_value(key.subindex, *value);
        }
        let root = tree.root_hash().unwrap();
        TestTree {
            tree,
            nodes: by_stem.into_values().collect(),
            root,
        }
    }

    /// Extension node for the stem node `node`, with its lowest present leaf. The
    /// node gets the label `stem`, which is the stem of `node` in a valid proof.
    fn extension_node(node: &StemNode, stem: Stem) -> ProofNode {
        let subindex = *node.values.keys().min().unwrap();
        let (value, subtree_siblings) = generate_stem_proof(node, subindex, &Sha256Hasher);
        ProofNode::Extension {
            stem,
            subindex,
            value: value.unwrap(),
            subtree_siblings,
        }
    }

    /// Hash of the subtree that holds `nodes`. The nodes are sorted by stem and
    /// share their first `depth` bits.
    fn subtree_hash_of(nodes: &[StemNode], depth: usize) -> B256 {
        let hasher = Sha256Hasher;
        match nodes {
            [] => B256::ZERO,
            [node] => node.hash(&hasher),
            _ => {
                let split = nodes.partition_point(|node| !node.stem.bit_at(depth));
                hasher.hash_64(
                    &subtree_hash_of(&nodes[..split], depth + 1),
                    &subtree_hash_of(&nodes[split..], depth + 1),
                )
            }
        }
    }

    /// Proof for `key` in the tree that holds `nodes` (sorted by stem). This is the
    /// reference prover of the tests; the crate has no prover for whole trees.
    fn tree_proof(nodes: &[StemNode], key: TreeKey) -> Proof {
        let hasher = Sha256Hasher;
        let mut internal = Vec::new();
        let mut rest = nodes;
        let mut depth = 0;
        while rest.len() > 1 {
            let split = rest.partition_point(|node| !node.stem.bit_at(depth));
            let (left, right) = rest.split_at(split);
            let (next, other, direction) = if key.stem.bit_at(depth) {
                (right, left, Direction::Right)
            } else {
                (left, right, Direction::Left)
            };
            internal.push(ProofNode::Internal {
                sibling: subtree_hash_of(other, depth + 1),
                direction,
            });
            rest = next;
            depth += 1;
        }
        internal.reverse();

        let (value, first) = match rest {
            [] => (None, None),
            [node] if node.stem == key.stem => {
                let (value, subtree_siblings) = generate_stem_proof(node, key.subindex, &hasher);
                let stem = node.stem;
                (
                    value,
                    Some(ProofNode::Stem {
                        stem,
                        subtree_siblings,
                    }),
                )
            }
            [node, ..] => (None, Some(extension_node(node, node.stem))),
        };
        Proof::new(key, value, first.into_iter().chain(internal).collect())
    }

    fn stem_with(first_byte: u8, fill: u8) -> Stem {
        let mut bytes = [fill; 31];
        bytes[0] = first_byte;
        Stem::new(bytes)
    }

    fn directions(proof: &Proof) -> Vec<Direction> {
        proof
            .path
            .iter()
            .filter_map(|node| match node {
                ProofNode::Internal { direction, .. } => Some(*direction),
                _ => None,
            })
            .collect()
    }

    fn assert_invalid(proof: &Proof, root: &B256) {
        let hasher = Sha256Hasher;
        assert!(
            matches!(proof.compute_root(&hasher), Err(UbtError::InvalidProof(_))),
            "compute_root must reject {proof:?}"
        );
        assert!(
            matches!(proof.verify(&hasher, root), Err(UbtError::InvalidProof(_))),
            "verify must reject {proof:?}"
        );
    }

    // Stems of the fixture, by their first bits: A = 00.., B = 010.., C = 0110..,
    // D = 0111... The right half of the tree (first bit 1) is empty.
    const STEM_A: (u8, u8) = (0b0000_0000, 0xa1);
    const STEM_B: (u8, u8) = (0b0100_0000, 0xb2);
    const STEM_C: (u8, u8) = (0b0110_0000, 0xc3);
    const STEM_D: (u8, u8) = (0b0111_0000, 0xd4);

    fn fixture_stem(stem: (u8, u8)) -> Stem {
        stem_with(stem.0, stem.1)
    }

    fn fixture_tree() -> TestTree {
        test_tree(&[
            (
                TreeKey::new(fixture_stem(STEM_A), 0),
                B256::repeat_byte(0x11),
            ),
            (TreeKey::new(fixture_stem(STEM_A), 200), B256::ZERO),
            (
                TreeKey::new(fixture_stem(STEM_B), 3),
                B256::repeat_byte(0x22),
            ),
            (
                TreeKey::new(fixture_stem(STEM_C), 7),
                B256::repeat_byte(0x33),
            ),
            (
                TreeKey::new(fixture_stem(STEM_C), 255),
                B256::repeat_byte(0x34),
            ),
            (
                TreeKey::new(fixture_stem(STEM_D), 128),
                B256::repeat_byte(0x44),
            ),
        ])
    }

    /// One proof of each kind verifies against `UnifiedBinaryTree::root_hash`, and
    /// the same proof with another value does not.
    #[test]
    fn test_tree_proofs_verify_for_each_kind_of_claim() {
        use Direction::{Left, Right};
        let hasher = Sha256Hasher;
        let fixture = fixture_tree();

        // Present leaf at the deepest stem node: 4 internal nodes, leaf to root.
        let present = tree_proof(&fixture.nodes, TreeKey::new(fixture_stem(STEM_D), 128));
        assert_eq!(present.value, Some(B256::repeat_byte(0x44)));
        assert!(matches!(present.path[0], ProofNode::Stem { .. }));
        assert_eq!(directions(&present), [Right, Right, Right, Left]);
        assert!(present.verify(&hasher, &fixture.root).unwrap());

        // Present zero leaf at a stem node at depth 2.
        let zero_leaf = tree_proof(&fixture.nodes, TreeKey::new(fixture_stem(STEM_A), 200));
        assert_eq!(zero_leaf.value, Some(B256::ZERO));
        assert_eq!(directions(&zero_leaf), [Left, Left]);
        assert!(zero_leaf.verify(&hasher, &fixture.root).unwrap());

        // Absent subindex of a present stem.
        let absent_subindex = tree_proof(&fixture.nodes, TreeKey::new(fixture_stem(STEM_C), 8));
        assert_eq!(absent_subindex.value, None);
        assert!(matches!(absent_subindex.path[0], ProofNode::Stem { .. }));
        assert_eq!(directions(&absent_subindex), [Left, Right, Right, Left]);
        assert!(absent_subindex.verify(&hasher, &fixture.root).unwrap());

        // Absent stem; the stem node of A is at its position.
        let other_stem = tree_proof(
            &fixture.nodes,
            TreeKey::new(stem_with(0b0000_1000, 0xe5), 0),
        );
        assert_eq!(other_stem.value, None);
        assert!(
            matches!(other_stem.path[0], ProofNode::Extension { stem, .. } if stem == fixture_stem(STEM_A))
        );
        assert_eq!(directions(&other_stem), [Left, Left]);
        assert!(other_stem.verify(&hasher, &fixture.root).unwrap());

        // Absent stem; its position is an empty subtree.
        let empty_position = tree_proof(
            &fixture.nodes,
            TreeKey::new(stem_with(0b1000_0000, 0xf6), 9),
        );
        assert_eq!(empty_position.value, None);
        assert_eq!(empty_position.path.len(), 1);
        assert_eq!(directions(&empty_position), [Right]);
        assert!(empty_position.verify(&hasher, &fixture.root).unwrap());

        for (proof, other_value) in [
            (&present, Some(B256::repeat_byte(0x45))),
            (&present, None),
            (&zero_leaf, None),
            (&absent_subindex, Some(B256::ZERO)),
        ] {
            let mut changed = proof.clone();
            changed.value = other_value;
            assert!(!changed.verify(&hasher, &fixture.root).unwrap());
        }
    }

    /// The empty tree has the root zero and the proof with an empty path. A tree
    /// with one stem has a stem proof with no internal nodes.
    #[test]
    fn test_tree_proofs_for_empty_tree_and_single_stem() {
        let hasher = Sha256Hasher;
        let key = TreeKey::new(stem_with(0x5a, 0x5b), 17);

        let empty = test_tree(&[]);
        assert_eq!(empty.root, B256::ZERO);
        let proof = tree_proof(&empty.nodes, key);
        assert_eq!((proof.value, proof.path.len()), (None, 0));
        assert!(proof.verify(&hasher, &empty.root).unwrap());

        let single = test_tree(&[(key, B256::repeat_byte(0x61))]);
        let proof = tree_proof(&single.nodes, key);
        assert_eq!(proof.path.len(), 1);
        assert!(proof.verify(&hasher, &single.root).unwrap());
        assert!(!proof.verify(&hasher, &empty.root).unwrap());
    }

    /// The zero stem has `stem || 0x00` equal to the hash of an empty subtree. Its
    /// proofs with empty siblings are valid.
    #[test]
    fn test_tree_proof_for_the_zero_stem_with_an_empty_sibling() {
        let hasher = Sha256Hasher;
        let zero_key = TreeKey::new(Stem::new([0u8; 31]), 1);
        let fixture = test_tree(&[
            (zero_key, B256::repeat_byte(0x71)),
            (
                TreeKey::new(stem_with(0b0100_0000, 0x72), 2),
                B256::repeat_byte(0x73),
            ),
        ]);
        let proof = tree_proof(&fixture.nodes, zero_key);
        let ProofNode::Internal { sibling, direction } = &proof.path[2] else {
            panic!("expected an internal node");
        };
        assert_eq!((*sibling, *direction), (B256::ZERO, Direction::Left));
        assert!(proof.verify(&hasher, &fixture.root).unwrap());

        let absent = tree_proof(&fixture.nodes, TreeKey::new(Stem::new([0u8; 31]), 2));
        assert_eq!(absent.value, None);
        assert!(absent.verify(&hasher, &fixture.root).unwrap());
    }

    /// Issue #19, case 1: a proof with an extension node claims no value.
    #[test]
    fn test_extension_proof_with_a_value_is_invalid() {
        let fixture = fixture_tree();
        let mut forged = tree_proof(
            &fixture.nodes,
            TreeKey::new(stem_with(0b0000_1000, 0xe5), 0),
        );
        assert!(matches!(forged.path[0], ProofNode::Extension { .. }));
        forged.value = Some(B256::repeat_byte(0xee));
        assert_invalid(&forged, &fixture.root);
    }

    /// Issue #19, case 2: a valid stem proof does not verify for a key of another stem.
    #[test]
    fn test_stem_proof_for_another_stem_is_invalid() {
        let key = TreeKey::new(Stem::new([7u8; 31]), 3);
        let single = test_tree(&[(key, B256::repeat_byte(0x42))]);
        let mut forged = tree_proof(&single.nodes, key);
        assert!(forged.verify(&Sha256Hasher, &single.root).unwrap());
        forged.key = TreeKey::new(Stem::new([9u8; 31]), 3);
        assert_invalid(&forged, &single.root);
    }

    /// The proof for an empty position on the right of the root does not verify for
    /// a present key on the left: the direction must agree with the key bit.
    #[test]
    fn test_direction_against_the_key_bit_is_invalid() {
        let hasher = Sha256Hasher;
        let fixture = fixture_tree();
        let present_key = TreeKey::new(fixture_stem(STEM_A), 0);
        assert!(fixture.tree.get(&present_key).is_some());

        let mut forged = tree_proof(
            &fixture.nodes,
            TreeKey::new(stem_with(0b1000_0000, 0xf6), 9),
        );
        assert!(forged.verify(&hasher, &fixture.root).unwrap());
        forged.key = present_key;
        assert_invalid(&forged, &fixture.root);

        let mut flipped = tree_proof(&fixture.nodes, TreeKey::new(fixture_stem(STEM_D), 128));
        let ProofNode::Internal { direction, .. } = &mut flipped.path[2] else {
            panic!("expected an internal node");
        };
        *direction = Direction::Left;
        assert_invalid(&flipped, &fixture.root);
    }

    /// The stem node of a present key, labelled with another stem in an extension
    /// node, does not prove that the key is absent: the verifier computes the stem
    /// node hash from the stem in the extension node.
    #[test]
    fn test_present_stem_relabelled_as_extension_does_not_verify() {
        let hasher = Sha256Hasher;
        let fixture = fixture_tree();
        let key = TreeKey::new(fixture_stem(STEM_D), 128);
        let valid = tree_proof(&fixture.nodes, key);
        let node = fixture
            .nodes
            .iter()
            .find(|node| node.stem == key.stem)
            .unwrap();

        let mut other_stem = *key.stem.as_bytes();
        other_stem[30] ^= 1;
        let mut path = vec![extension_node(node, Stem::new(other_stem))];
        path.extend_from_slice(&valid.path[1..]);
        let forged = Proof::new(key, None, path);
        assert!(!forged.verify(&hasher, &fixture.root).unwrap());
    }

    /// An extension stem that does not share the consumed prefix with the key is
    /// invalid. No tree of this crate has such a root; the root is built by hand
    /// with a stem node on the wrong side.
    #[test]
    fn test_extension_stem_off_the_key_path_is_invalid() {
        let hasher = Sha256Hasher;
        let mut misplaced = StemNode::new(stem_with(0b1000_0000, 0x55));
        misplaced.set_value(9, B256::repeat_byte(0x77));
        let sibling = B256::repeat_byte(0x99);
        let root = hasher.hash_64(&misplaced.hash(&hasher), &sibling);

        let forged = Proof::new(
            TreeKey::new(stem_with(0b0000_0000, 0x01), 0),
            None,
            vec![
                extension_node(&misplaced, misplaced.stem),
                ProofNode::Internal {
                    sibling,
                    direction: Direction::Left,
                },
            ],
        );
        assert_invalid(&forged, &root);

        // The same proof for a key on the right side of this root is valid.
        let mut on_the_path = forged.clone();
        on_the_path.key = TreeKey::new(stem_with(0b1000_0000, 0x56), 0);
        let ProofNode::Internal { direction, .. } = &mut on_the_path.path[1] else {
            panic!("expected an internal node");
        };
        *direction = Direction::Right;
        let root_on_the_right = hasher.hash_64(&sibling, &misplaced.hash(&hasher));
        assert!(on_the_path.verify(&hasher, &root_on_the_right).unwrap());
    }

    /// Issue #19, case 3: the path has at most one stem or extension node, as its
    /// first node, and at most 248 internal nodes. A value needs a stem node.
    #[test]
    fn test_path_shape_is_checked() {
        let hasher = Sha256Hasher;
        let key = TreeKey::new(Stem::new([0u8; 31]), 0);
        let internal = ProofNode::Internal {
            sibling: B256::ZERO,
            direction: Direction::Left,
        };
        let stem = ProofNode::Stem {
            stem: key.stem,
            subtree_siblings: vec![B256::ZERO; 8],
        };
        let mut other_node = StemNode::new(stem_with(0b0000_0000, 0x02));
        other_node.set_value(4, B256::repeat_byte(0x77));
        let extension = extension_node(&other_node, other_node.stem);
        let ProofNode::Extension {
            stem: other_stem,
            subindex,
            value: leaf,
            subtree_siblings,
        } = extension.clone()
        else {
            panic!("expected an extension node");
        };
        let short_extension = ProofNode::Extension {
            stem: other_stem,
            subindex,
            value: leaf,
            subtree_siblings: subtree_siblings[..7].to_vec(),
        };

        for path in [
            vec![stem.clone(), stem.clone()],
            vec![internal.clone(), stem.clone()],
            vec![internal.clone(), extension.clone()],
            vec![extension.clone(), extension.clone()],
            vec![extension.clone(), stem.clone()],
            vec![short_extension],
            vec![internal.clone(); 249],
        ] {
            assert_invalid(&Proof::new(key, None, path), &B256::ZERO);
        }

        let longest = Proof::new(key, None, vec![internal.clone(); 248]);
        assert_eq!(longest.compute_root(&hasher).unwrap(), B256::ZERO);

        let value = Some(B256::repeat_byte(0x42));
        assert_invalid(&Proof::new(key, value, vec![]), &B256::ZERO);
        assert_invalid(&Proof::new(key, value, vec![internal]), &B256::ZERO);
    }

    /// Deterministic generator for the property test (xorshift64).
    struct TestRng(u64);

    impl TestRng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn byte(&mut self) -> u8 {
            self.next().to_le_bytes()[3]
        }

        /// A stem with one of four first bytes, so that stems share prefixes and
        /// the tree has internal nodes with an empty side.
        fn stem(&mut self) -> Stem {
            let mut bytes = [0u8; 31];
            for byte in &mut bytes {
                *byte = self.byte();
            }
            bytes[0] = [0x00, 0x01, 0x40, 0xc0][usize::from(self.byte() % 4)];
            Stem::new(bytes)
        }
    }

    /// Entries of a random tree, and a pool of keys: the present keys, absent
    /// subindices of present stems, and absent stems (a neighbour of each present
    /// stem that differs in the last bit, and random stems).
    fn random_entries_and_key_pool(rng: &mut TestRng) -> (Vec<(TreeKey, B256)>, Vec<TreeKey>) {
        const SUBINDICES: [u8; 5] = [0, 1, 64, 128, 255];
        let mut entries = Vec::new();
        let mut pool = Vec::new();
        for _ in 0..24 {
            let stem = rng.stem();
            for subindex in SUBINDICES {
                let key = TreeKey::new(stem, subindex);
                match rng.byte() % 4 {
                    0 => entries.push((key, B256::ZERO)),
                    1 => entries.push((key, B256::repeat_byte(rng.byte()))),
                    _ => {}
                }
                pool.push(key);
            }
            let mut neighbour = *stem.as_bytes();
            neighbour[30] ^= 1;
            pool.push(TreeKey::new(Stem::new(neighbour), 0));
            pool.push(TreeKey::new(rng.stem(), 64));
        }
        (entries, pool)
    }

    /// Changed copies of a valid proof, each with a flag "must not verify": another
    /// value, a flipped direction, a dropped node, and the stem node relabelled as
    /// an extension node of a neighbour stem.
    fn changed_proofs(proof: &Proof, nodes: &[StemNode]) -> Vec<(Proof, bool)> {
        let mut changed = Vec::new();
        for value in [None, Some(B256::ZERO), Some(B256::repeat_byte(0x5c))] {
            let mut other_value = proof.clone();
            other_value.value = value;
            changed.push((other_value, false));
        }
        for index in 0..proof.path.len() {
            let mut flipped = proof.clone();
            if let ProofNode::Internal { direction, .. } = &mut flipped.path[index] {
                *direction = match direction {
                    Direction::Left => Direction::Right,
                    Direction::Right => Direction::Left,
                };
                changed.push((flipped, true));
            }
            let mut dropped = proof.clone();
            dropped.path.remove(index);
            changed.push((dropped, false));
        }
        if let Some(ProofNode::Stem { stem, .. }) = proof.path.first() {
            let node = nodes.iter().find(|node| node.stem == *stem).unwrap();
            let mut other_stem = *stem.as_bytes();
            other_stem[30] ^= 1;
            let mut relabelled = proof.clone();
            relabelled.value = None;
            relabelled.path[0] = extension_node(node, Stem::new(other_stem));
            changed.push((relabelled, true));
        }
        changed
    }

    /// Soundness over a random tree: a proof that verifies states a true claim.
    /// The reference prover gives a proof for each key of a pool. Each proof is
    /// then changed: another key of the pool, and the changes of `changed_proofs`.
    /// A changed proof that still verifies must state `tree.get(key) == value`.
    #[test]
    fn test_mutated_proofs_never_verify_a_false_claim() {
        let hasher = Sha256Hasher;
        let mut rng = TestRng(0x9e37_79b9_7f4a_7c15);
        let (entries, pool) = random_entries_and_key_pool(&mut rng);
        let fixture = test_tree(&entries);
        let accepted_claim_is_true = |proof: &Proof| {
            if matches!(proof.verify(&hasher, &fixture.root), Ok(true)) {
                assert_eq!(
                    fixture.tree.get(&proof.key),
                    proof.value,
                    "false claim: {proof:?}"
                );
                return true;
            }
            false
        };

        let mut relabelled_and_accepted = 0;
        for &key in &pool {
            let proof = tree_proof(&fixture.nodes, key);
            assert_eq!(proof.value, fixture.tree.get(&key));
            assert!(proof.verify(&hasher, &fixture.root).unwrap(), "{proof:?}");

            for &other_key in &pool {
                let mut changed = proof.clone();
                changed.key = other_key;
                if other_key != key && accepted_claim_is_true(&changed) {
                    relabelled_and_accepted += 1;
                }
            }
            for (changed, must_not_verify) in changed_proofs(&proof, &fixture.nodes) {
                let accepted = accepted_claim_is_true(&changed);
                assert!(!(must_not_verify && accepted), "verified: {changed:?}");
            }
        }
        // A proof of absence is valid for each key that leads to the same position,
        // so some relabelled proofs verify. This shows that the loop is not vacuous.
        assert!(relabelled_and_accepted > 0);
    }

    /// The hash of a stem node is `hash(stem || 0x00 || subtree_root)`, which is
    /// also `hash_64(stem || 0x00, subtree_root)`. A path with the sibling
    /// `stem || 0x00` reads the stem node of the key as an internal node, goes on
    /// into the 256-leaf subtree, and stops at an empty part of it. Such a path
    /// must not prove that a present key is absent.
    #[test]
    fn test_stem_node_of_the_key_read_as_internal_node_is_invalid() {
        let hasher = Sha256Hasher;
        let stem_p = stem_with(0b0000_0000, 0x01);
        let stem_q = stem_with(0b1110_0000, 0xff);
        let key = TreeKey::new(stem_q, 0);
        let fixture = test_tree(&[
            (TreeKey::new(stem_p, 5), B256::repeat_byte(0x10)),
            (key, B256::repeat_byte(0x20)),
        ]);
        let [node_p, node_q] = fixture.nodes.as_slice() else {
            panic!("expected two stem nodes");
        };
        assert!(tree_proof(&fixture.nodes, key)
            .verify(&hasher, &fixture.root)
            .unwrap());

        // The upper half of the subtree of Q is empty; its lower half is the top
        // sibling of each leaf of the upper half.
        let (_, siblings_of_255) = generate_stem_proof(node_q, 255, &hasher);
        let right = |sibling| ProofNode::Internal {
            sibling,
            direction: Direction::Right,
        };
        let path = vec![
            right(siblings_of_255[7]),
            right(stem_node_prefix(&stem_q)),
            right(node_p.hash(&hasher)),
        ];
        // Without the check of the sibling, this path gives the root of the tree.
        let subtree_root = hasher.hash_64(&siblings_of_255[7], &B256::ZERO);
        assert_eq!(
            hasher.hash_64(
                &node_p.hash(&hasher),
                &hasher.hash_64(&stem_node_prefix(&stem_q), &subtree_root)
            ),
            fixture.root
        );
        assert_invalid(&Proof::new(key, None, path), &fixture.root);
    }

    /// The stem node of the zero stem hashes as `hash(0^32 || subtree_root)`, which
    /// is also `hash_64(empty, subtree_root)`: an internal node with an empty left
    /// child. A path to that "empty position" must not prove that a present key of
    /// the zero stem is absent. The cost: the verifier also rejects the honest
    /// proof for an absent zero stem whose position is an empty subtree.
    #[test]
    fn test_zero_stem_node_read_as_internal_node_is_invalid() {
        let hasher = Sha256Hasher;
        let zero_stem = Stem::new([0u8; 31]);
        let key = TreeKey::new(zero_stem, 5);
        let internal = |sibling| ProofNode::Internal {
            sibling,
            direction: Direction::Left,
        };

        // A tree with the zero stem only, and a tree with the zero stem at depth 2.
        for other_entries in [
            vec![],
            vec![
                (
                    TreeKey::new(stem_with(0b0100_0000, 0x72), 2),
                    B256::repeat_byte(0x73),
                ),
                (
                    TreeKey::new(stem_with(0b1000_0000, 0x11), 3),
                    B256::repeat_byte(0x74),
                ),
            ],
        ] {
            let mut entries = vec![(key, B256::repeat_byte(0x42))];
            entries.extend(other_entries);
            let fixture = test_tree(&entries);
            let honest = tree_proof(&fixture.nodes, key);
            assert!(honest.verify(&hasher, &fixture.root).unwrap());

            let zero_node = fixture
                .nodes
                .iter()
                .find(|node| node.stem == zero_stem)
                .unwrap();
            let (leaf, siblings) = generate_stem_proof(zero_node, 5, &hasher);
            let leaf_hash = hasher.hash_32(&leaf.unwrap());
            let zero_subtree_root = subtree_root(&hasher, (5, leaf_hash), &siblings).unwrap();
            assert_eq!(
                hasher.hash_64(&B256::ZERO, &zero_subtree_root),
                zero_node.hash(&hasher)
            );

            let mut empty_position = vec![internal(zero_subtree_root)];
            empty_position.extend_from_slice(&honest.path[1..]);
            let mut empty_stem_node = vec![ProofNode::Stem {
                stem: zero_stem,
                subtree_siblings: vec![B256::ZERO; 8],
            }];
            empty_stem_node.extend_from_slice(&empty_position);
            // An empty level between the "empty position" and the stem node.
            let mut deeper = vec![internal(B256::ZERO)];
            deeper.extend_from_slice(&empty_position);
            for path in [empty_position, empty_stem_node, deeper] {
                assert_invalid(&Proof::new(key, None, path), &fixture.root);
            }
        }

        // The cost: an absent zero stem at an empty position cannot be proven.
        let without_zero_stem = test_tree(&[
            (
                TreeKey::new(stem_with(0b1000_0000, 0x11), 3),
                B256::repeat_byte(0x74),
            ),
            (
                TreeKey::new(stem_with(0b1100_0000, 0x12), 4),
                B256::repeat_byte(0x75),
            ),
        ]);
        let honest = tree_proof(&without_zero_stem.nodes, key);
        assert_eq!((honest.value, honest.path.len()), (None, 1));
        assert_invalid(&honest, &without_zero_stem.root);
    }

    /// `0^12 || address`, the first 32 bytes of the input of the key derivation.
    fn derivation_prefix(address: &Address) -> B256 {
        let mut prefix = B256::ZERO;
        prefix[12..].copy_from_slice(address.as_slice());
        prefix
    }

    /// The stem of an account header is `hash(0^12 || address || 0^32)[..31]`. For
    /// 1 of 256 addresses this hash ends in `0x00`, and then `stem || 0x00` is
    /// `hash_64(0^12 || address, empty)`. A path that reads the stem node as an
    /// internal node, goes into `stem || 0x00`, and reads that as an internal node
    /// with an empty right child must not prove that the account is absent.
    #[test]
    fn test_derived_stem_read_as_internal_node_is_invalid() {
        let hasher = Sha256Hasher;
        let (address, key) = (0u32..100_000)
            .map(|counter| {
                let mut bytes = [0x5au8; 20];
                bytes[..4].copy_from_slice(&counter.to_be_bytes());
                Address::from(bytes)
            })
            .map(|address| (address, get_basic_data_key(&address)))
            .find(|(address, key)| {
                let hash = hasher.hash_64(&derivation_prefix(address), &B256::ZERO);
                hash == stem_node_prefix(&key.stem) && !key.stem.bit_at(0) && key.stem.bit_at(1)
            })
            .unwrap();
        let fixture = test_tree(&[(key, B256::repeat_byte(0x64))]);
        assert!(tree_proof(&fixture.nodes, key)
            .verify(&hasher, &fixture.root)
            .unwrap());

        let (leaf, siblings) = generate_stem_proof(&fixture.nodes[0], key.subindex, &hasher);
        let leaf = (key.subindex, hasher.hash_32(&leaf.unwrap()));
        let key_subtree_root = subtree_root(&hasher, leaf, &siblings).unwrap();
        // Without the rules of the verifier, this path gives the root of the tree.
        let stem_as_hash = hasher.hash_64(&derivation_prefix(&address), &B256::ZERO);
        assert_eq!(
            hasher.hash_64(&stem_as_hash, &key_subtree_root),
            fixture.root
        );
        let path = vec![
            ProofNode::Internal {
                sibling: derivation_prefix(&address),
                direction: Direction::Right,
            },
            ProofNode::Internal {
                sibling: key_subtree_root,
                direction: Direction::Left,
            },
        ];
        assert_invalid(&Proof::new(key, None, path), &fixture.root);
    }

    /// A stem `hash(0^12 || address || x)[..31]` whose hash ends in `0x00` has a
    /// stem node that reads as an internal node over `hash_64(0^12 || address, x)`.
    /// A party that selects `x` (a storage slot) can make `x` the hash of a stem
    /// node that is not in the tree. A stem proof for that made-up node, below the
    /// sibling `0^12 || address`, must not prove that its key is present.
    /// (`get_storage_slot_key` also needs `x[0] == 0`; this test uses the stem
    /// without that condition, which needs 256 times fewer attempts.)
    #[test]
    fn test_made_up_stem_node_below_a_derived_stem_is_invalid() {
        let hasher = Sha256Hasher;
        let prefix = derivation_prefix(&Address::repeat_byte(0x11));
        let target = TreeKey::new(stem_with(0b0100_0000, 0x3c), 0);
        let (made_up, storage_stem) = (0u64..100_000)
            .map(|counter| {
                let mut value = [0xddu8; 32];
                value[..8].copy_from_slice(&counter.to_le_bytes());
                let mut node = StemNode::new(target.stem);
                node.set_value(target.subindex, B256::from(value));
                let hash = hasher.hash_64(&prefix, &node.hash(&hasher));
                (node, hash)
            })
            .find(|(_, hash)| hash[31] == 0)
            .map(|(node, hash)| (node, Stem::from_slice(&hash[..31])))
            .unwrap();
        let fixture = test_tree(&[(TreeKey::new(storage_stem, 0), B256::repeat_byte(0x01))]);
        assert_eq!(fixture.tree.get(&target), None);

        let (value, subtree_siblings) = generate_stem_proof(&made_up, target.subindex, &hasher);
        let (leaf, siblings) = generate_stem_proof(&fixture.nodes[0], 0, &hasher);
        let leaf = (0, hasher.hash_32(&leaf.unwrap()));
        let storage_subtree_root = subtree_root(&hasher, leaf, &siblings).unwrap();
        // Without the rules of the verifier, this path gives the root of the tree.
        let stem_as_hash = hasher.hash_64(&prefix, &made_up.hash(&hasher));
        assert_eq!(
            hasher.hash_64(&stem_as_hash, &storage_subtree_root),
            fixture.root
        );
        let path = vec![
            ProofNode::Stem {
                stem: target.stem,
                subtree_siblings,
            },
            ProofNode::Internal {
                sibling: prefix,
                direction: Direction::Right,
            },
            ProofNode::Internal {
                sibling: storage_subtree_root,
                direction: Direction::Left,
            },
        ];
        assert_invalid(&Proof::new(target, value, path), &fixture.root);
    }

    /// For an address that ends in `0x00`, the input `0^12 || address` of the key
    /// derivation is also `stem || 0x00` of the stem `0^12 || address[..19]`. A
    /// derived stem whose hash ends in `0x00` then has a stem node that reads as
    /// an internal node over a stem node of that low stem, with the `key` part of
    /// the derivation as its subtree root. A party that selects the `key` part (a
    /// storage slot) must not prove a made-up leaf of the low stem.
    /// (`get_storage_slot_key` also needs a `key` part that starts with `0x00`;
    /// this test uses the stem without that condition.)
    #[test]
    fn test_derivation_input_read_as_stem_node_is_invalid() {
        let hasher = Sha256Hasher;
        let mut address = [0x11u8; 20];
        address[19] = 0x00;
        let prefix = derivation_prefix(&Address::from(address));
        let target = TreeKey::new(Stem::from_slice(&prefix[..31]), 5);
        assert_eq!(stem_node_prefix(&target.stem), prefix);

        let (made_up, storage_stem) = (0u64..100_000)
            .map(|counter| {
                let mut value = [0xf4u8; 32];
                value[..8].copy_from_slice(&counter.to_le_bytes());
                let mut node = StemNode::new(target.stem);
                node.set_value(target.subindex, B256::from(value));
                let hash = node.hash(&hasher);
                (node, hash)
            })
            .find(|(_, hash)| hash[31] == 0)
            .map(|(node, hash)| (node, Stem::from_slice(&hash[..31])))
            .unwrap();
        let fixture = test_tree(&[(TreeKey::new(storage_stem, 0), B256::repeat_byte(0x01))]);
        assert_eq!(fixture.tree.get(&target), None);

        let (leaf, siblings) = generate_stem_proof(&fixture.nodes[0], 0, &hasher);
        let leaf = (0, hasher.hash_32(&leaf.unwrap()));
        let storage_subtree_root = subtree_root(&hasher, leaf, &siblings).unwrap();
        // Without the rules of the verifier, this path gives the root of the tree.
        assert_eq!(
            hasher.hash_64(&made_up.hash(&hasher), &storage_subtree_root),
            fixture.root
        );
        let (value, subtree_siblings) = generate_stem_proof(&made_up, target.subindex, &hasher);
        let path = vec![
            ProofNode::Stem {
                stem: target.stem,
                subtree_siblings,
            },
            ProofNode::Internal {
                sibling: storage_subtree_root,
                direction: Direction::Left,
            },
        ];
        assert_invalid(&Proof::new(target, value, path), &fixture.root);
    }

    /// The leaf in an extension node is part of the claim: with another leaf value
    /// the proof does not verify.
    #[test]
    fn test_extension_proof_with_a_changed_leaf_does_not_verify() {
        let hasher = Sha256Hasher;
        let fixture = fixture_tree();
        let mut proof = tree_proof(
            &fixture.nodes,
            TreeKey::new(stem_with(0b0000_1000, 0xe5), 0),
        );
        assert!(proof.verify(&hasher, &fixture.root).unwrap());
        let ProofNode::Extension { value, .. } = &mut proof.path[0] else {
            panic!("expected an extension node");
        };
        *value = B256::repeat_byte(0x12);
        assert!(!proof.verify(&hasher, &fixture.root).unwrap());
    }
}
