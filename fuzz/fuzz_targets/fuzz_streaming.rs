#![no_main]

use libfuzzer_sys::fuzz_target;
use ubt::{Blake3Hasher, StreamingTreeBuilder, TreeKey, UnifiedBinaryTree, B256};

/// Fuzz streaming builder with arbitrary sorted entries
/// Verifies streaming matches tree for any input
fuzz_target!(|data: &[u8]| {
    if data.len() < 64 {
        return;
    }

    // Parse entries from data (each entry is 64 bytes: 32 key + 32 value)
    let mut entries = Vec::new();
    let mut i = 0;
    while i + 64 <= data.len() {
        let key_bytes: [u8; 32] = data[i..i + 32].try_into().unwrap();
        let value_bytes: [u8; 32] = data[i + 32..i + 64].try_into().unwrap();

        let key = TreeKey::from_bytes(B256::from(key_bytes));
        let value = B256::from(value_bytes);

        // Skip zero values (they're treated as deletions)
        if value != B256::ZERO {
            entries.push((key, value));
        }

        i += 64;
    }

    if entries.is_empty() {
        return;
    }

    // Sort entries (streaming builder requires sorted input)
    entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

    // Deduplicate (keep last value per key)
    entries.dedup_by(|a, b| a.0 == b.0);

    // Build tree
    let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
    for (k, v) in &entries {
        tree.insert(*k, *v);
    }
    let tree_root = tree.root_hash().expect("tree depth within bounds");

    // Build via streaming
    let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
    let streaming_root = builder
        .build_root_hash(entries)
        .expect("tree depth within bounds");

    assert_eq!(tree_root, streaming_root, "streaming vs tree mismatch");
});
