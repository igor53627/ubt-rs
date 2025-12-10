# Complexity Analysis

This document describes the formal verification of time and space complexity bounds for UBT operations. The formal proofs are in [`formal/simulations/complexity.v`](../simulations/complexity.v).

## Overview

The Unified Binary Tree (UBT) has predictable complexity bounds that are critical for:
- **Gas cost estimation**: Ethereum execution requires bounded operation costs
- **Stateless validation**: Proof sizes must be bounded for light clients
- **Memory usage**: Node operators need predictable resource requirements

## Key Constants

| Constant | Value | Description |
|----------|-------|-------------|
| `MAX_DEPTH` | 248 | Maximum tree depth (31 stem bytes × 8 bits) |
| `STEM_SUBTREE_DEPTH` | 8 | Depth of stem subtree (1 subindex byte × 8 bits) |
| `TOTAL_MAX_DEPTH` | 256 | Maximum total path length |
| `STEM_BYTES` | 31 | Stem length in bytes |

## Complexity Bounds

### Tree Depth

**Theorem: `depth_bound`**
```
∀ t : SimTree, tree_depth t ≤ 256
```

The tree depth is bounded by the key size. Since stems are 31 bytes (248 bits), the tree portion has at most 248 levels. The stem subtree adds 8 levels for the subindex byte.

**Justification**: Keys are 32 bytes. The first 31 bytes determine the path through the binary tree to reach a stem node. The last byte (subindex) determines the path within the stem's 256-value subtree.

### Insert Preserves Depth

**Theorem: `insert_preserves_depth_bound`**
```
∀ t k v, tree_depth t ≤ 256 → tree_depth (insert t k v) ≤ 256
```

Insert operations cannot increase the tree depth beyond the maximum. This follows from the fixed key size—new entries either:
1. Add values to existing stems (no depth change)
2. Create new stems at their natural position (bounded by key bits)

**Corollary**: Any sequence of inserts maintains the depth bound:
```
∀ t ops, tree_depth t ≤ 256 → tree_depth (fold_left insert ops t) ≤ 256
```

### Proof Size is Logarithmic

**Theorem: `proof_size_logarithmic`**
```
∀ p : InclusionProof, inclusion_proof_size p ≤ 256
```

Merkle proofs have O(depth) size, which is O(log(key_space)):
- Tree proof: At most 248 sibling hashes
- Stem proof: Exactly 8 sibling hashes

**Byte Size Bound**:
```
inclusion_proof_size p × 33 ≤ 256 × 33 = 8,448 bytes
```

Each proof step is 33 bytes (32-byte hash + 1-byte direction).

### Stem Co-location Optimization

**Theorem: `stem_colocation_reduces_proofs`**
```
∀ k1 k2 : TreeKey,
  tk_stem k1 = tk_stem k2 →
  tk_subindex k1 ≠ tk_subindex k2 →
  ip_tree_proof p1 = ip_tree_proof p2 ∧
  witness_size (ip_stem_proof p1) ≤ 8 ∧
  witness_size (ip_stem_proof p2) ≤ 8
```

Keys sharing the same stem share the entire tree-level proof. Only the 8-level stem subtree proofs differ. This is the foundation for efficient batch proofs in EIP-7864.

**Practical Impact**:
- Account data (nonce, balance, code hash, first storage slots) share a stem
- Proving all basic account data needs only 1 tree path + multiple 8-level paths
- Worst case: 248 + 4×8 = 280 hash nodes vs 4×256 = 1024 without co-location

### MultiProof Efficiency

**Theorem: `multiproof_shared_stem_efficiency`**
```
∀ mp : MultiProof,
  (∀ k1 k2 ∈ mp_keys mp, tk_stem k1 = tk_stem k2) →
  multiproof_hash_count mp ≤ 248 + |mp_keys mp| × 8
```

When all keys share a stem, the multiproof is dramatically more efficient than individual proofs.

**Theorem: `multiproof_more_efficient`**
```
∀ mp : MultiProof,
  |mp_keys mp| > 1 →
  multiproof_hash_count mp < |mp_keys mp| × 256
```

Multiproofs are always more efficient than individual proofs due to deduplication.

## Time Complexity

### Insert Operation

| Mode | Complexity | Notes |
|------|------------|-------|
| Deferred | O(1) | Hash computation deferred |
| Immediate | O(D) | D = depth to changed stem |

### Root Hash Computation

| Mode | Complexity | Notes |
|------|------------|-------|
| Full rebuild | O(S log S) | S = stem count, sort + tree build |
| Incremental | O(D × C) | D = 248 depth, C = changed stems |

Incremental mode is optimal for block-by-block processing where few stems change per block.

### Proof Generation

| Operation | Complexity |
|-----------|------------|
| Single proof | O(D) |
| MultiProof (n keys) | O(D + n × 8) best case |
| MultiProof (n keys, different stems) | O(n × D) |

## Space Complexity

### Tree Storage

**Theorem: `tree_space_linear_in_entries`**
```
stem_count t ≤ tree_size t
```

Memory usage is O(entries), not O(key_space). The sparse tree representation only stores non-empty values.

### Incremental Mode Cache

```
cache_size = O(stems × MAX_DEPTH)
```

The node hash cache stores intermediate hashes for incremental updates. This is approximately 2× the stem count in internal nodes.

### Proof Storage

| Proof Type | Size Bound |
|------------|------------|
| Single inclusion | ≤ 8,448 bytes |
| Single exclusion | ≤ 8,192 bytes |
| MultiProof (n keys, same stem) | ≤ 8,192 + n × 264 bytes |

## Comparison with Hexary Patricia Trie

| Property | UBT | Hexary Patricia |
|----------|-----|-----------------|
| Max depth | 256 | ~64 |
| Proof size | O(256) | O(64) but larger nodes |
| Co-location | Native (256 values/stem) | None |
| ZK-friendly | Yes (binary) | No (16-way branch) |

While UBT has deeper trees, the binary structure and co-location make it more efficient for ZK proofs and batch operations.

## Formal Proof Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `depth_bound` | ✓ Proven | Direct from definition |
| `insert_preserves_depth_bound` | ✓ Proven | Structural induction |
| `inserts_preserve_depth_bound` | ✓ Proven | Corollary |
| `proof_size_logarithmic` | Admitted | Requires proof gen axiom |
| `stem_colocation_shared_tree_proof` | Admitted | Structural property |
| `stem_colocation_reduces_proofs` | Admitted | Follows from above |
| `multiproof_shared_stem_efficiency` | Admitted | Deduplication property |
| `multiproof_more_efficient` | Admitted | Deduplication property |
| `tree_space_linear_in_entries` | ✓ Proven | Structural induction |

## References

- [EIP-7864](https://eips.ethereum.org/EIPS/eip-7864): Ethereum State Using a Unified Binary Tree
- [`src/tree.rs`](../../src/tree.rs): Rust implementation of tree operations
- [`src/proof.rs`](../../src/proof.rs): Rust implementation of proof generation
- [`formal/simulations/tree.v`](../simulations/tree.v): Formal tree specification
