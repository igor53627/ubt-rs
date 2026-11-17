# Unified Binary Tree (UBT)

[![Crates.io](https://img.shields.io/crates/v/ubt.svg)](https://crates.io/crates/ubt)
[![Documentation](https://docs.rs/ubt/badge.svg)](https://docs.rs/ubt)
[![Rust CI](https://github.com/igor53627/ubt-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/igor53627/ubt-rs/actions/workflows/rust.yml)
[![Ask DeepWiki](https://img.shields.io/badge/Ask-DeepWiki-0366d6)](https://deepwiki.com/igor53627/ubt-rs)
[![zread](https://img.shields.io/badge/Ask_Zread-_.svg?style=flat-square&color=00b0aa&labelColor=000000&logo=data%3Aimage%2Fsvg%2Bxml%3Bbase64%2CPHN2ZyB3aWR0aD0iMTYiIGhlaWdodD0iMTYiIHZpZXdCb3g9IjAgMCAxNiAxNiIgZmlsbD0ibm9uZSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj4KPHBhdGggZD0iTTQuOTYxNTYgMS42MDAxSDIuMjQxNTZDMS44ODgxIDEuNjAwMSAxLjYwMTU2IDEuODg2NjQgMS42MDE1NiAyLjI0MDFWNC45NjAxQzEuNjAxNTYgNS4zMTM1NiAxLjg4ODEgNS42MDAxIDIuMjQxNTYgNS42MDAxSDQuOTYxNTZDNS4zMTUwMiA1LjYwMDEgNS42MDE1NiA1LjMxMzU2IDUuNjAxNTYgNC45NjAxVjIuMjQwMUM1LjYwMTU2IDEuODg2NjQgNS4zMTUwMiAxLjYwMDEgNC45NjE1NiAxLjYwMDFaIiBmaWxsPSIjZmZmIi8%2BCjxwYXRoIGQ9Ik00Ljk2MTU2IDEwLjM5OTlIMi4yNDE1NkMxLjg4ODEgMTAuMzk5OSAxLjYwMTU2IDEwLjY4NjQgMS42MDE1NiAxMS4wMzk5VjEzLjc1OTlDMS42MDE1NiAxNC4xMTM0IDEuODg4MSAxNC4zOTk5IDIuMjQxNTYgMTQuMzk5OUg0Ljk2MTU2QzUuMzE1MDIgMTQuMzk5OSA1LjYwMTU2IDE0LjExMzQgNS42MDE1NiAxMy43NTk5VjExLjAzOTlDNS42MDE1NiAxMC42ODY0IDUuMzE1MDIgMTAuMzk5OSA0Ljk2MTU2IDEwLjM5OTlaIiBmaWxsPSIjZmZmIi8%2BCjxwYXRoIGQ9Ik0xMy43NTg0IDEuNjAwMUgxMS4wMzg0QzEwLjY4NSAxLjYwMDEgMTAuMzk4NCAxLjg4NjY0IDEwLjM5ODQgMi4yNDAxVjQuOTYwMUMxMC4zOTg0IDUuMzEzNTYgMTAuNjg1IDUuNjAwMSAxMS4wMzg0IDUuNjAwMUgxMy43NTg0QzE0LjExMTkgNS42MDAxIDE0LjM5ODQgNS4zMTM1NiAxNC4zOTg0IDQuOTYwMVYyLjI0MDFDMTQuMzk4NCAxLjg4NjY0IDE0LjExMTkgMS42MDAxIDEzLjc1ODQgMS42MDAxWiIgZmlsbD0iI2ZmZiIvPgo8cGF0aCBkPSJNNCAxMkwxMiA0TDQgMTJaIiBmaWxsPSIjZmZmIi8%2BCjxwYXRoIGQ9Ik00IDEyTDEyIDQiIHN0cm9rZT0iI2ZmZiIgc3Ryb2tlLXdpZHRoPSIxLjUiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIvPgo8L3N2Zz4K&logoColor=ffffff)](https://zread.ai/igor53627/ubt-rs)
[![Proof Verification](https://github.com/igor53627/ubt-rs/actions/workflows/proofs.yml/badge.svg)](https://github.com/igor53627/ubt-rs/actions/workflows/proofs.yml)


A Rust implementation of [EIP-7864: Ethereum state using a unified binary tree](https://eips.ethereum.org/EIPS/eip-7864).

> **Scope:** this crate implements the unified binary tree with 32-byte keys and 256-value stem nodes, as go-ethereum implemented it in `trie/bintrie`. It does not implement the EIP-8297 partitioned binary tree, and it does not follow the June 2026 revision of the EIP-7864 text. See [Scope and Direction](#scope-and-direction).

## Overview

This crate provides a binary tree structure intended to replace Ethereum's hexary patricia trees. Key features:

- **Single tree**: Account and storage tries are merged into a single tree with 32-byte keys
- **Code chunking**: Contract bytecode is chunked and stored in the tree
- **Data co-location**: Related data (nonce, balance, first storage slots, first code chunks) are grouped together in 256-value subtrees to reduce branch openings
- **ZK-friendly**: Designed for efficient proving in ZK circuits
- **Parallel hashing**: Uses rayon for concurrent stem hash computation (enabled by default)
- **Incremental updates**: O(D*C) root updates instead of O(S log S) full rebuilds
- **Pluggable storage**: `NodeStore` trait allows custom backends (RocksDB, redb) for persistent state
- **Formally verified**: Core operations proven correct using the Rocq proof assistant

## Requirements

- Rust 1.85+ (MSRV). `rust-toolchain.toml` pins the toolchain for local development.

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
let root = tree.root_hash().unwrap();

// Retrieve a value
let value = tree.get(&key);
```

### Zero Values and Deletion

A value of 32 zero bytes is a present leaf, as in go-ethereum. `insert(key, B256::ZERO)` keeps the leaf and the stem, `get` returns `Some(B256::ZERO)`, and the leaf is hashed. This is the equivalent of the zero writes of go-ethereum `DeleteStorage` and `DeleteAccount`.

`delete(&key)` removes the leaf, and removes the stem when it has no values left. The tree is then in the state "never written" for that key. go-ethereum has no such operation.

```rust
use ubt::{UnifiedBinaryTree, TreeKey, Sha256Hasher, B256};

let mut tree: UnifiedBinaryTree<Sha256Hasher> = UnifiedBinaryTree::new();
let key = TreeKey::from_bytes(B256::repeat_byte(0x01));

tree.insert(key, B256::ZERO);
assert_eq!(tree.get(&key), Some(B256::ZERO));
assert_ne!(tree.root_hash().unwrap(), B256::ZERO);

tree.delete(&key);
assert_eq!(tree.get(&key), None);
assert_eq!(tree.root_hash().unwrap(), B256::ZERO);
```

### Batch Operations

For inserting many values efficiently, use batch operations:

```rust
use ubt::{UnifiedBinaryTree, TreeKey, Blake3Hasher, B256, Stem};

// Pre-allocate for known capacity
let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::with_capacity(1_000_000);

// Batch insert (single tree rebuild at the end)
let entries: Vec<(TreeKey, B256)> = vec![/* ... */];
tree.insert_batch(entries).unwrap();
```

### Streaming Tree Builder (Memory-Efficient)

For large migrations where memory is constrained, use the streaming builder:

```rust
use ubt::{StreamingTreeBuilder, TreeKey, Blake3Hasher, B256, Stem};

// Entries MUST be sorted by (stem, subindex)
let mut entries: Vec<(TreeKey, B256)> = vec![/* ... */];
entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

let builder: StreamingTreeBuilder<Blake3Hasher> = StreamingTreeBuilder::new();
let root = builder.build_root_hash(entries).unwrap();
```

The streaming builder computes the root hash without keeping the full tree in memory.

### Incremental Mode

For block-by-block state updates where only a small subset of stems change:

```rust
use ubt::{UnifiedBinaryTree, Blake3Hasher, TreeKey, B256};

let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
// ... initial inserts ...
tree.root_hash().unwrap(); // Full rebuild

// Enable incremental mode for subsequent updates
tree.enable_incremental_mode();
tree.root_hash().unwrap(); // Populates intermediate node cache

// Future updates reuse cached intermediate hashes: O(D*C) hashing work
// (root_hash() still does O(S log S) stem sort; D=248, C=changed stems)
tree.insert(TreeKey::from_bytes(B256::repeat_byte(0x02)), B256::repeat_byte(0x43));
tree.root_hash().unwrap(); // Only recomputes paths to changed stems
```

See [docs/incremental-updates.md](docs/incremental-updates.md) for benchmarks and when to use each mode.

### Custom Storage Backend

The tree is generic over the `NodeStore` trait, which abstracts stem node storage. The default `InMemoryStore` uses a `HashMap`. To integrate with a persistent database, implement `NodeStore` for your backend:

```rust
use ubt::{NodeStore, UnifiedBinaryTree, Blake3Hasher};

// Implement NodeStore for your backend
// struct MyStore { /* RocksDB handle, etc. */ }
// impl NodeStore for MyStore { /* ... */ }

// Construct tree with custom store
// let store = MyStore::open("path/to/db");
// let mut tree = UnifiedBinaryTree::<Blake3Hasher, MyStore>::with_store(store);

// Access the store directly for backend-specific operations (e.g., commit/flush)
// tree.store_mut().flush();
```

The `with_store()` constructor correctly handles both empty and pre-populated stores. You can also extract the store back with `into_store()`.

### Binary Codec

The `codec` module provides compact binary encode/decode for all node types, suitable for persistent storage backends:

| Tag | Type | Size |
|-----|------|------|
| `0x00` | Empty | 1 byte |
| `0x01` | Internal | 65 bytes |
| `0x02` | Stem | 64 + N×32 bytes (bitmap-based) |
| `0x03` | Leaf | 33 bytes |

```rust
use ubt::{Stem, StemNode, B256};
use ubt::codec::{encode_stem_node, decode_stem_node};

let mut node = StemNode::new(Stem::new([0u8; 31]));
node.set_value(0, B256::repeat_byte(0x42));

let bytes = encode_stem_node(&node);
let decoded = decode_stem_node(&bytes).unwrap();
assert_eq!(decoded.get_value(0), node.get_value(0));
```

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

## Features

| Feature | Default | Description |
|---------|---------|-------------|
| `parallel` | Yes | Parallel stem hashing via rayon |
| `serde` | No | Serialization support for tree types |
| `simulate` | No | Enables the simulation stress-test binary |

To disable default features:

```toml
[dependencies]
ubt = { version = "0.5", default-features = false }
```

To run the simulation stress-test binary:

```bash
cargo run --bin simulate --features simulate -- --seed 12345 --ops 10000
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

A custom implementation must follow the contract in the `Hasher` docs: `hash_32` has no zero rule (the hash of 32 zero bytes is not zero), and `hash_64` returns zero when both inputs are zero.

## go-ethereum Compatibility

The crate was compared with go-ethereum `trie/bintrie` at commit `b0f9324c` (2026-11-09). That is the last commit that contains the package: commit `ddaa6957` (2026-11-10) removed the EIP-7864 binary trie in favour of the EIP-8297 partitioned binary tree (`trie/pbt`).

With `Sha256Hasher`, the crate gives the same tree keys, leaf contents, and root hashes as go-ethereum at that commit, also for trees that contain zero values. The comparison ran the go-ethereum hashing and key derivation code against the crate, and it includes the roots that go-ethereum pins in `TestBinaryGenesisCommit` and `TestMerkleizeMultipleEntries`.

Known differences:

| Area | go-ethereum `trie/bintrie` | This crate |
|------|----------------------------|------------|
| Hash function | SHA-256 | BLAKE3 by default; use `Sha256Hasher` for go-ethereum roots |
| Zero values | A leaf that holds 32 zero bytes is present and hashes to `sha256(0^32)`. Deletion writes zero; stems are never removed. | The same in versions after 0.5.2: `insert(key, B256::ZERO)` stores a present leaf that is hashed, and the stem stays. The crate also has `delete`, which go-ethereum does not have: it removes the value and a stem with no values left. |
| Node encoding | Stem tag `1`, internal tag `2`, bitmap MSB-first, internal nodes stored in groups of up to 8 levels | `ubt::codec`: stem tag `2`, internal tag `1`, bitmap LSB-first, one internal node per record. Not wire-compatible. |
| Account API, node database, iterator, witness | Present | Not implemented |
| Proof verification, streaming builder, incremental mode | Not implemented (`Prove` panics) | Present |

A tree that contains a zero-valued leaf, for example a storage slot set to zero or a deleted account, has the same root as in go-ethereum. To follow go-ethereum `DeleteStorage` and `DeleteAccount`, write zero values with `insert(key, B256::ZERO)`. `delete(&key)` restores the state "never written" for the key and gives a root that go-ethereum cannot reach from the same sequence of writes. Versions up to 0.5.2 treated a zero value as absent and gave different roots for these trees.

### Scope and Direction

Decision (2026-11-17): `ubt` stays an implementation of the unified binary tree. EIP-8297 support is not planned for this crate.

- The reference for this crate is go-ethereum `trie/bintrie` at commit `b0f9324c`, the last commit before go-ethereum removed the package.
- The EIP-7864 text changed on 2026-06-24 (ethereum/EIPs pull request 11832). The current text puts a storage-type byte first in the key and allows keys of arbitrary length. This crate implements the earlier design with fixed 32-byte keys.
- EIP-8297 (Partitioned Binary Tree, Draft, created 2026-06-11) is a different tree. It has variable-length keys with a zone byte (34 and 66 bytes), no stem node with a fixed 256-leaf subtree, tagged leaf and branch hashes with a bit prefix, and code keyed by code hash. Of this crate, only the code chunking and the basic data layout apply to it. An implementation of EIP-8297 belongs in a separate crate.

## Formal Verification Status

**Status:** **VERIFICATION COMPLETE** (December 2025)

[![Proof Verification](https://github.com/igor53627/ubt-rs/actions/workflows/proofs.yml/badge.svg)](https://github.com/igor53627/ubt-rs/actions/workflows/proofs.yml)
[![Verification Summary](https://img.shields.io/badge/verification-95%25%20confidence-brightgreen)](formal/docs/VERIFICATION_SUMMARY.md)
[![Qed Count](https://img.shields.io/badge/Qed-641%20proofs-blue)](formal/docs/VERIFICATION_SUMMARY.md)

This crate includes formal verification using [rocq-of-rust](https://github.com/formal-land/rocq-of-rust) and the Rocq proof assistant.

### Key Metrics

| Metric | Initial | Final | Change |
|--------|---------|-------|--------|
| **Theorems (Qed)** | ~20 | **641** | +3105% |
| **Total Axioms** | 50+ | **186** | All documented |
| **Linking Axioms** | N/A | **46** | Minimal trust base |
| **Admitted** | 10+ | **79** | 0 `admit.` tactics in linking/simulations/proofs; 79 `Admitted.` theorems in generated code (`formal/src/`) ([details](formal/docs/ADMITS_TRACKING.md)) |
| **QuickChick Properties** | 5 | **22 CI / 50 total** | 11k/500k tests |
| **Verification Confidence** | - | **95%** | Complete |

### Operation Verification Summary

| Component | Status | Confidence |
|-----------|--------|------------|
| new_executes | AXIOM (`linking/operations.v`) | 100% |
| delete_executes | **PROVEN** | 100% |
| get_executes | AXIOM; `get_executes_derived` is proven from lower-level axioms | 90% |
| insert_executes | AXIOM; `insert_executes_derived` is proven from lower-level axioms | 95% |
| root_hash_executes | DERIVED | 75% |

### Proven Properties

| Theorem | Status | Scope |
|---------|--------|-------|
| Empty tree has zero hash | Proven | Rust API |
| Hash is deterministic | Proven | Rust API |
| Get from empty returns None | Proven | Rust API |
| Get after insert returns value | Proven | Rust API |
| Insert doesn't affect other keys | Proven | Rust API |
| Delete removes value | Proven | Rust API |
| Keys with same stem share subtree | Proven | Rust API |
| Insert preserves well-formedness | Proven | Rust API |
| Order independence (all cases) | Proven | Rust API |
| Inclusion proof soundness | Axiom | Formal model |
| Exclusion proof soundness | Axiom | Formal model |
| Batch verification soundness | Proven | Formal model |
| EUF-MPA security | Proven | Formal model |
| Accumulator soundness | Proven | Formal model |

**Note:** Properties marked "Formal model" are proven in the Rocq formal verification but the corresponding Rust APIs (batch verification, accumulators) are not yet exposed.

**Note:** The translated Rust code in `formal/src/` and the linking layer model the crate source before 0.5.0. They do not cover `NodeStore`, the binary codec, or the V3 key derivation. The Rocq simulation model (`sim_set` in `formal/simulations/tree.v`) still removes the entry on a zero write, and therefore models the behaviour before zero values became present leaves.

### Axiom Classification

| Category | Count | Description |
|----------|-------|-------------|
| **Total Axioms** | 186 | All Axiom declarations in linking+simulations (209 with specs and proofs) |
| **Linking Axioms** | 46 | Axioms in formal/linking/ layer |
| **IRREDUCIBLE** | 25 | Minimal trust base (monad laws, crypto, stdlib) |
| **Parameters (non-axioms)** | 77 | Type/function abstractions, tracked separately |

**Trust assumptions:**
- **Monad Laws:** Standard mathematical properties (high confidence)
- **RocqOfRust Translation:** Assumes correct Rust-to-Rocq translation
- **HashMap/Iterator Semantics:** Standard library behavior

**Future work:** Full M monad interpreter to eliminate simulation axioms (was tracked in rocq-of-rust-interp#1; that repository no longer exists).

See [formal/docs/VERIFICATION_SUMMARY.md](formal/docs/VERIFICATION_SUMMARY.md) for complete verification summary.

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
├── lib/             # Local M monad interpreter library
└── src/             # Auto-generated translation (24k lines)
```

### Dependencies

- [rocq-of-rust](https://github.com/formal-land/rocq-of-rust) - Rust to Rocq translation

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
│   ├── tree/        # Main tree structure (mod, hash)
│   ├── store.rs     # NodeStore trait and InMemoryStore
│   ├── codec.rs     # Compact binary node encoding
│   ├── node.rs      # Node types
│   ├── key.rs       # Tree keys and stems
│   ├── hash.rs      # Hash trait and implementations
│   ├── merkle.rs    # Shared stem hash and root recursion
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
