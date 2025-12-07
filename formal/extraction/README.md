# OCaml Extraction for UBT

This directory contains the OCaml extraction of the UBT simulation layer.

## Building

From the `formal/` directory:

```bash
# Set up Rocq environment
eval $(opam env --switch=rocq-9)

# Build simulations and extract to OCaml
make extract
```

This generates:
- `extraction/extracted.ml` - OCaml implementation
- `extraction/extracted.mli` - OCaml interface

## Running Tests (Optional)

If you have OCaml installed:

```bash
cd extraction
ocamlopt extracted.ml test_extracted.ml -o test_ubt
./test_ubt
```

Or with ocamlfind (if needed):
```bash
cd extraction
ocamlfind ocamlopt -package zarith -linkpkg extracted.ml test_extracted.ml -o test_ubt
./test_ubt
```

## Axioms Requiring Implementation

The extracted code contains placeholder implementations for cryptographic primitives. 
For production use, replace these with actual implementations:

### Hash Functions (from tree.v and crypto.v)

| Function | Signature | Placeholder | Production Implementation |
|----------|-----------|-------------|---------------------------|
| `hash_value` | `bytes32 -> bytes32` | Identity function | Poseidon/Pedersen hash |
| `hash_pair` | `bytes32 -> bytes32 -> bytes32` | Concatenate + truncate | Merkle tree internal node hash |
| `hash_stem` | `stem -> bytes32 -> bytes32` | Concatenate + truncate | Verkle stem commitment |

### Verkle Commitment Functions (from verkle.v)

| Function | Signature | Placeholder | Production Implementation |
|----------|-----------|-------------|---------------------------|
| `verkle_commit` | `value list -> VerkleCommitment` | Returns empty list | KZG/IPA polynomial commitment |
| `verkle_open` | `VerkleCommitment -> Z -> Value -> VerkleProof` | Returns unit | Opening proof generation |
| `verkle_verify` | `VerkleCommitment -> Z -> Value -> VerkleProof -> bool` | Returns true | Polynomial commitment verification |

### Other Axioms

| Axiom | Location | Purpose |
|-------|----------|---------|
| `stems_well_formed` | tree.v | All stems have length 31 bytes |

## Code Structure

The extracted code includes:

### Types
- `stem` - 31-byte key prefix
- `treeKey` - Full 32-byte key (stem + subindex)
- `simTree` - Functional tree data structure
- `subIndexMap` - Map from subindex to value
- `merkleStep`, `merkleWitness` - Merkle proof types

### Core Operations
- `sim_tree_get` - Get value for key
- `sim_tree_insert` - Insert key-value pair
- `sim_tree_delete` - Delete key

### Predicates
- `is_zero_value` - Check if value is all zeros
- `stem_eq` - Stem equality

## FFI Integration with Rust UBT

See [../docs/FFI_INTEGRATION.md](../docs/FFI_INTEGRATION.md) for complete documentation.

### Quick Start

```bash
# Build Rust FFI library
cd ffi/rust && cargo build --release

# Test FFI library (4 tests)
cargo test
```

### Files

| File | Purpose |
|------|---------|
| `ffi/ffi_bridge.ml` | OCaml bridge for type conversions |
| `ffi/ffi_stubs.ml` | Ctypes bindings (requires ctypes package) |
| `ffi/rust/src/lib.rs` | C-compatible hash function exports |
| `ffi/rust/Cargo.toml` | Rust crate configuration |

## Notes

1. The extraction uses OCaml `int` for Coq `Z` (via `ExtrOcamlZInt`)
2. Lists are extracted to OCaml lists
3. The Verkle operations are stubs - implement for full functionality
4. Hash functions have FFI implementations in `ffi/rust/`
