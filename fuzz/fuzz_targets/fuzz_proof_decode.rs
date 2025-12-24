#![no_main]

use libfuzzer_sys::fuzz_target;
use ubt::{Blake3Hasher, Hasher, Proof, ProofNode, Direction, Stem, TreeKey, B256};

/// Fuzz proof verification with arbitrary proof data
/// Tests that malformed proofs don't cause panics
fuzz_target!(|data: &[u8]| {
    if data.len() < 64 {
        return;
    }

    // Parse key from first 32 bytes
    let key_bytes: [u8; 32] = data[0..32].try_into().unwrap();
    let key = TreeKey::from_bytes(B256::from(key_bytes));

    // Parse value from next 32 bytes (or None if all zeros)
    let value_bytes: [u8; 32] = data[32..64].try_into().unwrap();
    let value = if value_bytes == [0u8; 32] {
        None
    } else {
        Some(B256::from(value_bytes))
    };

    // Build path from remaining data
    let mut path = Vec::new();
    let mut i = 64;

    while i + 33 <= data.len() {
        let node_type = data[i];
        match node_type % 3 {
            0 => {
                // Internal node
                if i + 33 <= data.len() {
                    let sibling: [u8; 32] = data[i + 1..i + 33].try_into().unwrap();
                    let direction = if data[i] & 0x80 != 0 {
                        Direction::Right
                    } else {
                        Direction::Left
                    };
                    path.push(ProofNode::Internal {
                        sibling: B256::from(sibling),
                        direction,
                    });
                    i += 33;
                } else {
                    break;
                }
            }
            1 => {
                // Extension node
                if i + 64 <= data.len() {
                    let stem_bytes: [u8; 31] = data[i + 1..i + 32].try_into().unwrap();
                    let hash_bytes: [u8; 32] = data[i + 32..i + 64].try_into().unwrap();
                    path.push(ProofNode::Extension {
                        stem: Stem::new(stem_bytes),
                        stem_hash: B256::from(hash_bytes),
                    });
                    i += 64;
                } else {
                    break;
                }
            }
            2 => {
                // Stem node with subtree siblings
                if i + 32 <= data.len() {
                    let stem_bytes: [u8; 31] = data[i + 1..i + 32].try_into().unwrap();
                    let mut subtree_siblings = Vec::new();

                    // Parse up to 8 siblings
                    let mut j = i + 32;
                    while j + 32 <= data.len() && subtree_siblings.len() < 8 {
                        let sib: [u8; 32] = data[j..j + 32].try_into().unwrap();
                        subtree_siblings.push(B256::from(sib));
                        j += 32;
                    }

                    path.push(ProofNode::Stem {
                        stem: Stem::new(stem_bytes),
                        subtree_siblings,
                    });
                    i = j;
                } else {
                    break;
                }
            }
            _ => unreachable!(),
        }
    }

    // Create proof and try to compute root (should not panic)
    let proof = Proof::new(key, value, path);
    let hasher = Blake3Hasher;

    // These should not panic even with malformed input
    let _ = proof.compute_root(&hasher);
    let _ = proof.verify(&hasher, &B256::ZERO);
    let _ = proof.size();
});
