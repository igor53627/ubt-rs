#![no_main]

use libfuzzer_sys::fuzz_target;
use ubt::{Blake3Hasher, TreeKey, UnifiedBinaryTree, B256};

/// Fuzz arbitrary tree operations
/// Tests that no sequence of operations causes panics or undefined behavior
fuzz_target!(|data: &[u8]| {
    if data.len() < 33 {
        return;
    }

    let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

    // Interpret data as a sequence of operations
    let mut i = 0;
    while i + 33 <= data.len() {
        let op = data[i];
        let key_bytes: [u8; 32] = data[i + 1..i + 33].try_into().unwrap();
        let key = TreeKey::from_bytes(B256::from(key_bytes));

        match op % 4 {
            0 => {
                // Insert with value derived from key
                let value = B256::from(key_bytes);
                tree.insert(key, value);
            }
            1 => {
                // Insert zero (delete semantics)
                tree.insert(key, B256::ZERO);
            }
            2 => {
                // Delete
                tree.delete(&key);
            }
            3 => {
                // Get
                let _ = tree.get(&key);
            }
            _ => unreachable!(),
        }

        i += 33;
    }

    // Always compute root hash at end
    let _ = tree.root_hash();
});
