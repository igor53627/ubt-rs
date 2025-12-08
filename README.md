# Unified Binary Tree (UBT)

A Rust implementation of [EIP-7864: Ethereum state using a unified binary tree](https://eips.ethereum.org/EIPS/eip-7864).

## Overview

This crate provides a binary tree structure intended to replace Ethereum's hexary patricia trees. Key features:

- **Single tree**: Account and storage tries are merged into a single tree with 32-byte keys
- **Code chunking**: Contract bytecode is chunked and stored in the tree
- **Data co-location**: Related data (nonce, balance, first storage slots, first code chunks) are grouped together in 256-value subtrees to reduce branch openings
- **ZK-friendly**: Designed for efficient proving in ZK circuits
- **Formally verified**: Core operations proven correct using the Rocq proof assistant

## Tree Structure

The tree uses 32-byte keys where:
- First 31 bytes: **stem** (defines the subtree path)
- Last byte: **subindex** (position within the 256-value subtree)

### Node Types

| Node Type | Description | Hash Formula |
|-----------|-------------|--------------|
| `InternalNode` | Branching node with left/right children | `hash(left_hash \|\| right_hash)` |
| `StemNode` | Roots a 256-value subtree, contains stem | `hash(stem \|\| 0x00 \|\| hash(left_hash \|\| right_hash))` |
| `LeafNode` | Contains a 32-byte value | `hash(value)` |
| `EmptyNode` | Represents empty subtree | `0x00...00` (32 zero bytes) |

### Tree Embedding (State Layout)

Each Ethereum account maps to tree keys as follows:

| Subindex | Content |
|----------|---------|
| 0 | Basic data (version, code size, nonce, balance) |
| 1 | Code hash |
| 2-63 | Reserved |
| 64-127 | First 64 storage slots |
| 128-255 | First 128 code chunks |

Storage slots >= 64 and code chunks >= 128 are stored in separate stems.

## Usage

```rust
use ubt::{UnifiedBinaryTree, TreeKey, Blake3Hasher, B256};

// Create a new tree
let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();

// Insert a value
let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
tree.insert(key, B256::repeat_byte(0x42));

// Get the root hash
let root = tree.root_hash();

// Retrieve a value
let value = tree.get(&key);
```

### Batch Operations

For inserting many values efficiently, use batch operations:

```rust
use ubt::{UnifiedBinaryTree, TreeKey, Blake3Hasher, B256, Stem};

// Pre-allocate for known capacity
let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(1_000_000);

// Batch insert (single tree rebuild at the end)
let entries: Vec<(TreeKey, B256)> = vec![/* ... */];
tree.insert_batch(entries);
```

### Streaming Tree Builder (Memory-Efficient)

For large migrations where memory is constrained, use the streaming builder:

```rust
use ubt::{StreamingTreeBuilder, TreeKey, Blake3Hasher, B256, Stem};

// Entries MUST be sorted by (stem, subindex)
let mut entries: Vec<(TreeKey, B256)> = vec![/* ... */];
entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
let root = builder.build_root_hash(entries);
```

The streaming builder computes the root hash without keeping the full tree in memory.

### Working with Accounts

```rust
use ubt::{AccountStem, BasicDataLeaf, chunkify_code, Address, U256};

let address = Address::repeat_byte(0x42);
let account = AccountStem::new(address);

// Get tree key for basic data (nonce, balance)
let basic_data_key = account.basic_data_key();

// Get tree key for storage slot
let storage_key = account.storage_key(U256::from(0));

// Chunkify contract code
let bytecode = vec![0x60, 0x80, 0x60, 0x40, 0x52];
let chunks = chunkify_code(&bytecode);
```

## Hash Function

> **Note**: The hash function is not finalized per EIP-7864. This implementation uses BLAKE3 as a reference. Candidates include Keccak and Poseidon2.

The hasher is abstracted via the `Hasher` trait, allowing different implementations:

```rust
use ubt::{Hasher, Blake3Hasher};

// Custom hasher implementation
struct MyHasher;
impl Hasher for MyHasher {
    // ... implement hash methods
}
```

## Formal Verification

**Status:** **VERIFICATION COMPLETE** (December 2024)

This crate includes formal verification using [rocq-of-rust](https://github.com/formal-land/rocq-of-rust) and the Rocq proof assistant. All proofs are complete with **0 admits remaining**.

[![Proof Verification](https://github.com/igor53627/ubt-rs/actions/workflows/proofs.yml/badge.svg)](https://github.com/igor53627/ubt-rs/actions/workflows/proofs.yml)

### Proven Properties

| Theorem | Status |
|---------|--------|
| Empty tree has zero hash | Proven |
| Hash is deterministic | Proven |
| Get from empty returns None | Proven |
| Get after insert returns value | Proven |
| Insert doesn't affect other keys | Proven |
| Delete removes value | Proven |
| Keys with same stem share subtree | Proven |
| Insert preserves well-formedness | Proven |
| Order independence (all cases) | Proven |
| Inclusion proof soundness | Proven |
| Exclusion proof soundness | Proven |
| Batch verification soundness | Proven |
| EUF-MPA security | Proven |
| Accumulator soundness | Proven |

### Verification Status

| Metric | Count | Notes |
|--------|-------|-------|
| Axioms | **66** | Crypto (26), Verkle (14), Linking (18), Security (8) |
| Parameters | **26** | Abstract types and functions |
| Admitted proofs | **0** | All closed |
| QuickChick tests | 50,000 | 5 properties, 10k each |
| OCaml extraction | 10/10 | All tests passing |
| FFI bridge | Complete | Rust ↔ OCaml validated |

**Axiom categories:**
- **Cryptographic**: Hash determinism, collision resistance, zero-value properties
- **Verkle commitments**: Binding, hiding, multi-open correctness
- **Rust linking**: Execution semantics, refinement relations (all verified)

### Building Proofs

```bash
# Activate Rocq environment
eval $(opam env --switch=rocq-9)

# Build proofs
cd formal
make

# Build linking layer
make linking

# Run axiom audit
bash scripts/count_axioms.sh
```

See [formal/README.md](formal/README.md) for detailed setup instructions.

### Verification Structure

```
formal/
├── specs/           # Mathematical specifications
├── simulations/     # Idiomatic Rocq implementation + security proofs
├── proofs/          # Correctness proofs + QuickChick tests
├── linking/         # Rust-to-Rocq refinement (complete)
└── src/             # Auto-generated translation (24k lines)
```

## Comparison with MPT

| Feature | MPT (Current) | UBT (EIP-7864) |
|---------|---------------|----------------|
| Tree type | Hexary (16-ary) | Binary (2-ary) |
| Proof size | ~3840 bytes (worst case) | ~800 bytes (typical) |
| Encoding | RLP | Raw 32-byte values |
| Code storage | Hash only | Chunked in tree |
| ZK proving | Expensive | Efficient |

## Project Structure

```
ubt/
├── src/             # Rust implementation
│   ├── tree.rs      # Main tree structure
│   ├── node.rs      # Node types
│   ├── key.rs       # Tree keys and stems
│   ├── hash.rs      # Hash trait and implementations
│   ├── embedding.rs # State embedding
│   ├── streaming.rs # Streaming tree builder
│   └── ...
├── formal/          # Formal verification
│   ├── specs/       # Rocq specifications
│   ├── simulations/ # Idiomatic Rocq
│   ├── proofs/      # Correctness proofs
│   └── src/         # Translated Rust
└── spec/            # EIP-7864 specification
```

## Contributing

When contributing to this project, please follow these style guidelines:

- **No emojis**: Use ASCII symbols instead of unicode emojis
  - Use `[x]` or `(done)` instead of checkmarks
  - Use `[!]` or `(warn)` instead of warning signs
  - Use `->` instead of arrows

## License

Licensed under either of Apache License, Version 2.0 or MIT license at your option.
