# FFI Integration: OCaml Extracted Code ↔ Rust UBT

This document describes the integration between the formally verified OCaml code
(extracted from Rocq/Coq proofs) and the production Rust UBT implementation.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Rocq/Coq Proofs                                 │
│  (specs/tree.v, simulations/sim_tree.v, proofs/*)                       │
│                                                                         │
│  • Type definitions (treeKey, stem, simTree)                            │
│  • Core operations (sim_tree_get, sim_tree_insert, sim_tree_delete)     │
│  • Correctness proofs (get-insert, delete semantics)                    │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │ make extract
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    OCaml Extracted Code                                 │
│  (extraction/extracted.ml)                                              │
│                                                                         │
│  • Pure functional tree operations                                      │
│  • Placeholder hash functions                                           │
│  • 10/10 tests pass                                                     │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                      FFI Bridge Layer                                   │
│  (extraction/ffi/ffi_bridge.ml)                                         │
│                                                                         │
│  • Type conversions (OCaml list ↔ Bytes.t)                              │
│  • Wrapped tree operations for C-compatible calling                     │
│  • Hash function entry points                                           │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │ Ctypes FFI calls
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    Rust FFI Library                                     │
│  (extraction/ffi/rust/src/lib.rs)                                       │
│                                                                         │
│  • C-compatible hash functions                                          │
│  • BLAKE3 and SHA256 implementations                                    │
│  • Safe wrappers around slice operations                                │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │ Direct Rust calls
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    UBT Rust Crate                                       │
│  (/Users/user/pse/paradigm/ubt/src/)                                    │
│                                                                         │
│  • Full tree implementation (tree.rs)                                   │
│  • Key types (key.rs: Stem, TreeKey)                                    │
│  • Node types (node.rs: Node, StemNode, InternalNode)                   │
│  • Hash traits and implementations (hash.rs)                            │
└─────────────────────────────────────────────────────────────────────────┘
```

## Type Correspondence

### OCaml Extracted → Rust UBT

| OCaml Type (extracted.ml) | Rust Type (ubt/src/) | Notes |
|---------------------------|----------------------|-------|
| `stem = byte0 list` (31 bytes) | `Stem([u8; 31])` | 31-byte key prefix |
| `subIndex = byte0` | `SubIndex = u8` | 0-255 subindex |
| `treeKey = {tk_stem; tk_subindex}` | `TreeKey {stem, subindex}` | Full 32-byte key |
| `value = bytes0` (32 bytes) | `B256` | 32-byte value |
| `simTree = stemMap` | `HashMap<Stem, StemNode>` | Stem → values mapping |
| `subIndexMap = (subIndex*value) list` | `HashMap<SubIndex, B256>` | Sparse value storage |
| `simNode` variants | `Node` enum | `SimEmpty`→`Empty`, `SimInternal`→`Internal`, etc. |

### Memory Layout for FFI

```
┌─────────────────────────────────────────────────────────────────┐
│ Tree Key (32 bytes)                                             │
├────────────────────────────────────┬────────────────────────────┤
│ Stem (31 bytes)                    │ SubIndex (1 byte)          │
│ bytes[0..31]                       │ bytes[31]                  │
└────────────────────────────────────┴────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│ Value (32 bytes)                                                │
│ bytes[0..32]                                                    │
└─────────────────────────────────────────────────────────────────┘
```

## FFI Functions

### Hash Functions (Rust → OCaml)

| C Function | Input | Output | Purpose |
|------------|-------|--------|---------|
| `rust_blake3_hash_32` | 32 bytes | 32 bytes | Hash a single value |
| `rust_blake3_hash_64` | 32 + 32 bytes | 32 bytes | Internal node hash |
| `rust_blake3_hash_stem` | 31 + 32 bytes | 32 bytes | Stem node hash |
| `rust_sha256_hash_32` | 32 bytes | 32 bytes | SHA256 alternative |
| `rust_sha256_hash_64` | 32 + 32 bytes | 32 bytes | SHA256 internal hash |

### OCaml Bridge Functions

| Function | Type | Purpose |
|----------|------|---------|
| `ffi_empty_tree` | `unit -> ffi_tree` | Create empty tree |
| `ffi_get` | `ffi_tree -> bytes -> bytes` | Get value for key |
| `ffi_insert` | `ffi_tree -> bytes -> bytes -> ffi_tree` | Insert key-value |
| `ffi_delete` | `ffi_tree -> bytes -> ffi_tree` | Delete key |
| `ffi_contains` | `ffi_tree -> bytes -> bool` | Check if key exists |

## Building

### 1. Build Rust FFI Library

```bash
cd /Users/user/pse/paradigm/ubt/formal/extraction/ffi/rust
cargo build --release
```

This produces:
- `target/release/libubt_ffi.dylib` (macOS)
- `target/release/libubt_ffi.so` (Linux)
- `target/release/libubt_ffi.a` (static library)

### 2. Build OCaml with Ctypes (optional)

```bash
# Install dependencies
opam install ctypes ctypes-foreign

# Compile with FFI support
cd /Users/user/pse/paradigm/ubt/formal/extraction
ocamlfind ocamlopt -package ctypes,ctypes-foreign -linkpkg \
  extracted.ml ffi/ffi_bridge.ml ffi/ffi_stubs.ml \
  -o test_ffi
```

### 3. Run Without Ctypes (placeholder mode)

The FFI bridge includes placeholder implementations that work without
the Rust library, useful for testing the extraction layer:

```bash
cd /Users/user/pse/paradigm/ubt/formal
eval $(opam env --switch=rocq-9)
make extract
cd extraction
ocamlopt extracted.ml test_extracted.ml -o test_ubt
./test_ubt  # 10/10 tests pass
```

## Integration Strategies

### Strategy A: OCaml as Reference Implementation

Use the extracted OCaml code as a reference oracle for testing the Rust implementation:

```rust
// In Rust tests
#[test]
fn test_against_ocaml_oracle() {
    // 1. Run operation in Rust
    let rust_result = tree.insert(key, value);
    
    // 2. Run same operation via FFI in OCaml extracted code
    let ocaml_result = ffi_insert(&mut ocaml_tree, key_bytes, value_bytes);
    
    // 3. Compare root hashes
    assert_eq!(rust_result.root_hash(), ocaml_result.root_hash());
}
```

### Strategy B: Rust Hashing in OCaml

Replace extracted placeholder hash functions with real Rust implementations:

```ocaml
(* In OCaml *)
let hash_value_real v =
  let bytes = value_to_bytes v in
  let result = Ffi_stubs.blake3_hash_32 bytes in
  list_of_bytes result
```

### Strategy C: Full Bidirectional FFI

Create complete interop where either side can call the other:

```
OCaml: tree operations, proof verification
Rust: hashing, serialization, network I/O
```

## Axiom Implementation Status

The extracted code requires these axioms to be implemented for production:

| Axiom | Current Status | Implementation Location |
|-------|----------------|------------------------|
| `hash_value` | Placeholder (identity) | `ffi/rust/src/lib.rs::rust_blake3_hash_32` |
| `hash_pair` | Placeholder (concat+truncate) | `ffi/rust/src/lib.rs::rust_blake3_hash_64` |
| `hash_stem` | Placeholder (concat+truncate) | `ffi/rust/src/lib.rs::rust_blake3_hash_stem` |
| `verkle_commit` | Placeholder (empty list) | Not yet implemented |
| `verkle_open` | Placeholder (unit) | Not yet implemented |
| `verkle_verify` | Placeholder (true) | Not yet implemented |

## Testing Cross-Implementation Consistency

### Property-Based Testing

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn insert_get_matches_ocaml(
        stem in prop::array::uniform31(any::<u8>()),
        subindex in any::<u8>(),
        value in prop::array::uniform32(any::<u8>())
    ) {
        let key = TreeKey::new(Stem::new(stem), subindex);
        
        // Rust operation
        let mut rust_tree = UnifiedBinaryTree::new();
        rust_tree.insert(key, B256::from(value));
        let rust_get = rust_tree.get(&key);
        
        // OCaml operation via FFI
        let ocaml_tree = ffi_empty_tree();
        let ocaml_tree = ffi_insert(ocaml_tree, key.to_bytes(), value);
        let ocaml_get = ffi_get(ocaml_tree, key.to_bytes());
        
        prop_assert_eq!(rust_get.map(|v| v.0), Some(ocaml_get));
    }
}
```

### Differential Fuzzing

```bash
# Generate random operations
cargo fuzz run diff_fuzz -- \
  --rust-impl target/release/libubt.so \
  --ocaml-impl extraction/ffi/rust/target/release/libubt_ffi.so
```

## Security Considerations

1. **Memory Safety**: All FFI functions use fixed-size buffers to prevent overflows
2. **Input Validation**: Assert correct lengths before calling Rust functions
3. **No Allocation Across Boundary**: Each side manages its own memory
4. **Deterministic Hashing**: Same inputs must produce same outputs across implementations

## Future Work

1. **Verkle Commitment FFI**: Implement IPA/KZG polynomial commitment FFI
2. **Proof Serialization**: Binary format for cross-language proof exchange
3. **Parallel Hashing**: Batch hash operations for tree rebuilds
4. **WASM Target**: Compile Rust FFI to WebAssembly for browser verification
