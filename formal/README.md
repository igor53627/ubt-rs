# Formal Verification of UBT (EIP-7864)

This directory contains formal verification artifacts for the Unified Binary Tree implementation.

## Status

| Component | Status | Description |
|-----------|--------|-------------|
| Specifications | ✅ Complete | Mathematical specs in Rocq |
| Simulations | ✅ Complete | Idiomatic Rocq tree operations |
| Proofs | ✅ Complete | Simulation-level proofs |
| Translation | ✅ Compiles | rocq-of-rust output (24,556 lines, 8 files) |
| Linking | ❌ Pending | Translation ↔ Simulation equivalence |

### Proven Properties

The following theorems are proven at the simulation level:

| Theorem | Statement |
|---------|-----------|
| Empty Tree Zero Hash | `sim_node_hash SimEmpty = zero32` |
| Hash Determinism | `sim_node_hash n = sim_node_hash n` |
| Get from Empty | `sim_tree_get empty_tree k = None` |
| Get-Insert Same | `sim_tree_get (insert t k v) k = Some v` |
| Get-Insert Other (Stem) | Different stems don't interfere |
| Get-Insert Other (Subindex) | Same stem, different subindex don't interfere |
| Delete Correctness | `sim_tree_get (delete t k) k = None` |
| Stem Co-location | Keys sharing stem share StemNode |
| Well-formedness | Insert preserves tree structure |

### Partially Proven

- Order independence (some admits in edge cases)
- Stem equality transitivity (requires length assumptions)

## Quick Start

```bash
# Activate Rocq environment
eval $(opam env --switch=rocq-9)

# Build all proofs
make

# Check what's installed
make check-deps
```

## Directory Structure

```
formal/
├── README.md           # This file
├── INSTALL.md          # Detailed setup instructions
├── Makefile            # Build automation
├── specs/              # Mathematical specifications
│   ├── tree_spec.v     # Tree operation specs (191 lines)
│   └── embedding_spec.v # State embedding specs (175 lines)
├── simulations/        # Idiomatic Rocq implementation
│   └── tree.v          # Tree operations (550 lines)
├── proofs/             # Formal proofs
│   └── correctness.v   # Main theorems (230 lines)
└── src/                # Auto-generated translation
    ├── tree.v          # ~4,000 lines
    ├── node.v          # ~6,000 lines
    ├── hash.v          # ~3,000 lines
    ├── key.v           # ~3,500 lines
    ├── embedding.v     # ~3,000 lines
    ├── code.v          # ~2,000 lines
    ├── proof.v         # ~2,500 lines
    └── error.v         # ~500 lines
```

## Verification Approach

We follow the rocq-of-rust recommended workflow:

```
┌─────────────────┐     ┌─────────────────┐
│   Rust Code     │────▶│   Translation   │ ✅ Compiles
│   (ubt crate)   │     │   (src/*.v)     │
└─────────────────┘     └────────┬────────┘
                                 │ (pending)
                                 ▼
┌─────────────────┐     ┌─────────────────┐
│  Specification  │◀────│   Simulation    │ ✅ Proven
│  (specs/*.v)    │     │ (simulations/)  │
└─────────────────┘     └────────┬────────┘
                                 │
                                 ▼
                        ┌─────────────────┐
                        │     Proofs      │ ✅ Complete
                        │  (proofs/*.v)   │
                        └─────────────────┘
```

1. **Translation**: `cargo +nightly-2024-12-07 rocq-of-rust` generates verbose Rocq
2. **Simulation**: Hand-written idiomatic Rocq that mirrors Rust semantics
3. **Linking** (pending): Prove translation ≈ simulation
4. **Specification**: Define what the code should do
5. **Proofs**: Prove simulation satisfies specification

## Build Targets

```bash
make              # Build specs, simulations, proofs
make translation  # Build translated Rust code
make translate    # Re-run rocq-of-rust translation
make check-deps   # Verify dependencies
make clean        # Remove generated files
```

## Hash Functions

Hash functions (SHA256) are axiomatized since we can't reason about cryptographic internals:

```coq
Parameter hash_value : Value -> Bytes32.
Parameter hash_pair : Bytes32 -> Bytes32 -> Bytes32.

Axiom hash_zero_value : hash_value zero32 = zero32.
Axiom hash_zero_pair : hash_pair zero32 zero32 = zero32.
```

## Requirements

- **Rocq 9.x** via opam switch `rocq-9`
- **RocqOfRust library** (compiled from rocq-of-rust repo)
- **rocq-of-rust** (for translation, requires nightly-2024-12-07)

See [INSTALL.md](INSTALL.md) for detailed setup instructions.

## Next Steps

To complete full verification:

1. **Create linking proofs** - Show translation matches simulation behavior
2. **Prove no-panic** - Analyze monadic structure for termination
3. **Complete order independence** - Finish admitted cases
4. **Merkle proof verification** - Prove witness correctness

## References

- [EIP-7864 Specification](../spec/EIP-7864-spec.md)
- [rocq-of-rust](https://github.com/formal-land/rocq-of-rust)
- [Rocq Reference](https://rocq-prover.org/doc/)
