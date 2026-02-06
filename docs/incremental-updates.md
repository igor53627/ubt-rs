# Incremental Updates vs Full Rebuild

The `UnifiedBinaryTree` supports two modes for computing root hashes:

1. **Full Rebuild** (default): Recomputes the entire tree structure on each `root_hash()` call
2. **Incremental Mode**: Caches intermediate node hashes, only recomputes paths affected by changes

## Quick Reference

| Workload | Recommended Mode | Reason |
|----------|------------------|--------|
| Initial tree population | Full Rebuild | No cache to benefit from |
| Bulk import (millions of keys) | Full Rebuild | Many stems change, cache overhead not worth it |
| Block-by-block execution | Incremental | Few stems change per block, O(D*C) vs O(S log S) |
| State sync / snapshot load | Full Rebuild | One-time bulk load |
| Transaction replay | Incremental | Sequential blocks, few changes each |

## Complexity Analysis

### Full Rebuild Mode

- **Insert**: O(1) - just marks stem dirty
- **root_hash()**: O(S log S) where S = total stems
  - Sort all stem hashes: O(S log S)
  - Build tree recursively: O(S)

### Incremental Mode

- **Insert**: O(1) - marks stem dirty
- **root_hash()** (first call after enable): O(S log S) - populates cache
- **root_hash()** (subsequent): O(S log S) for sorting + O(D * C) for path updates
  - Sorting all stems dominates for large S
  - Path traversal benefits from cached sibling hashes
  - Main benefit: skips recomputing unchanged subtree hashes

## Usage

```rust
use ubt::{UnifiedBinaryTree, Blake3Hasher, TreeKey, B256};

let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

// Phase 1: Bulk loading (use full rebuild - default)
for (key, value) in initial_data {
    tree.insert(key, value);
}
let initial_root = tree.root_hash().unwrap(); // Full rebuild

// Phase 2: Block execution (switch to incremental)
tree.enable_incremental_mode();
tree.root_hash().unwrap(); // Populates the cache

// Now each block's updates are O(D * C) instead of O(S log S)
for block in blocks {
    for (key, value) in block.state_changes() {
        tree.insert(key, value);
    }
    let block_root = tree.root_hash().unwrap(); // Incremental update
}

// Phase 3: Back to bulk mode if needed
tree.disable_incremental_mode(); // Clears cache, saves memory
```

## Memory Overhead

Incremental mode maintains a cache of intermediate node hashes:

- **Cache size**: Approximately 2 * S entries (upper bound)
- **Entry size**: `(usize, B256)` key + `B256` value = ~72 bytes per entry
- **Total overhead**: ~144 * S bytes

For 100,000 stems: ~14.4 MB cache overhead

Pre-allocate if you know the tree size:

```rust
let tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(100_000);
```

## When NOT to Use Incremental Mode

1. **High churn rate**: If > 10% of stems change per update, full rebuild may be faster
2. **Memory constrained**: Cache adds ~200 bytes per stem
3. **One-time computation**: No benefit if you only compute root once
4. **Infrequent updates**: If updates are rare, cache memory isn't justified

## Benchmark Results

Run benchmarks with:

```bash
cargo bench --bench incremental_vs_rebuild
```

Results (Apple M-series, release build):

### Single Update (1 stem changed)

| Tree Size | Full Rebuild | Incremental | Speedup |
|-----------|--------------|-------------|---------|
| 1,000 stems | 340 us | 295 us | 1.15x |
| 10,000 stems | 4.3 ms | 3.7 ms | 1.16x |
| 50,000 stems | 28.8 ms | 26.0 ms | 1.11x |
| 100,000 stems | 65 ms | 60 ms | 1.08x |

### Batch Update (realistic block simulation)

| Scenario | Full Rebuild | Incremental | Speedup |
|----------|--------------|-------------|---------|
| 10k stems, 100 changes | 4.3 ms | 3.9 ms | 1.10x |
| 10k stems, 1000 changes | 5.5 ms | 5.0 ms | 1.10x |
| 50k stems, 500 changes | 30 ms | 28 ms | 1.07x |
| 100k stems, 500 changes | 68 ms | 61 ms | 1.11x |
| 100k stems, 1000 changes | 68 ms | 63 ms | 1.08x |

### Analysis

The incremental mode provides modest (~10-15%) speedups in the current implementation.
The speedup is limited because:

1. **Dirty stem detection overhead**: Checking if a subtree contains dirty stems
   involves HashSet lookups for each dirty stem at each tree level
2. **Cache miss penalty**: Large trees have poor cache locality
3. **Sorted stem list**: The current implementation still sorts all stems

The incremental mode shines when:
- Tree size is large (100k+ stems)
- Changes per block are small (<1% of stems)
- Multiple consecutive blocks are processed (cache stays warm)

## Implementation Details

The incremental mode works by:

1. Caching all intermediate node hashes keyed by `(depth, path_prefix)`
2. On update, identifying which stems are dirty
3. Walking only paths containing dirty stems
4. Using cached sibling hashes for unchanged subtrees
5. Updating cache entries along recomputed paths

See `rebuild_root_incremental()` and `incremental_hash_update()` in `src/tree.rs`.
