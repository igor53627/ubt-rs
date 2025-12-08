# UBT Formal Verification Documentation

**Status:** ✅ **VERIFICATION COMPLETE** (December 2024)

This is the formal verification of the Unified Binary Tree (UBT) implementation for Ethereum's EIP-7864.

## Overview

The UBT is a Verkle-compatible binary tree structure designed to replace the Merkle Patricia Trie in Ethereum's state management. This verification proves key correctness properties of the Rust implementation.

All proofs are complete with **0 admits remaining**.

> **Trust Summary**  
> This verification relies on the following main assumptions:
> - **Cryptographic hardness**: Hash collision resistance (SHA256/Poseidon), Verkle polynomial binding (KZG/IPA)
> - **Tool trust**: Rocq soundness, rocq-of-rust translation correctness
> - **Library trust**: Rust stdlib, alloy-primitives
> 
> See [Axiom Audit](axiom_audit.md) for complete details.

## Quick Start

```bash
# Build the verification
eval $(opam env --switch=rocq-9)
make clean && make all && make linking

# Generate HTML documentation
make docs
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    VERIFICATION STACK                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────┐                                                │
│  │   Rust      │  Original implementation (../src/)             │
│  │   Code      │  tree.rs, node.rs, key.rs, hash.rs, etc.       │
│  └──────┬──────┘                                                │
│         │ rocq-of-rust                                          │
│         ▼                                                        │
│  ┌─────────────┐                                                │
│  │ Translation │  Auto-generated Rocq (src/*.v)                 │
│  │   Layer     │  Monadic, verbose, machine-checked              │
│  └──────┬──────┘                                                │
│         │ Link instances                                         │
│         ▼                                                        │
│  ┌─────────────┐                                                │
│  │  Linking    │  Type correspondence (linking/*.v)             │
│  │   Layer     │  Rust type ↔ Simulation type                   │
│  └──────┬──────┘                                                │
│         │ Refinement proofs                                      │
│         ▼                                                        │
│  ┌─────────────┐                                                │
│  │ Simulation  │  Idiomatic Rocq (simulations/*.v)              │
│  │   Layer     │  Pure functional, easy to reason about          │
│  └──────┬──────┘                                                │
│         │ Correctness proofs                                     │
│         ▼                                                        │
│  ┌─────────────┐                                                │
│  │   Specs     │  Mathematical specification (specs/*.v)        │
│  │   Layer     │  What the code should do                       │
│  └─────────────┘                                                │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Documentation Links

### Generated HTML (after `make docs`)

- [Table of Contents](html/toc.html) - Browse all modules
- [Tree Specification](html/UBT.Specs.tree_spec.html) - Core tree types and operations
- [Embedding Specification](html/UBT.Specs.embedding_spec.html) - State key derivation
- [Cryptographic Primitives](html/UBT.Sim.crypto.html) - Hash function axioms
- [Tree Operations](html/UBT.Sim.tree.html) - Main implementation
- [Verkle Support](html/UBT.Sim.verkle.html) - Polynomial commitment proofs
- [Correctness Proofs](html/UBT.Proofs.correctness.html) - Main theorems
- [Examples](html/UBT.Proofs.examples.html) - Concrete test cases

### Manual Documentation

- [README](../README.md) - Project overview
- [INSTALL](../INSTALL.md) - Setup instructions
- [Linking Layer Setup](LINKING_LAYER_SETUP.md) - RocqOfRust setup and linking layer docs
- [Verification Scope](VERIFICATION_SCOPE.md) - What is and isn't formally verified
- [Verification Status](VERIFICATION_STATUS.md) - What's proven vs. axiomatized
- [Axiom Audit](axiom_audit.md) - Detailed audit of all 67 axioms
- [Theorems Reference](THEOREMS.md) - Complete theorem documentation including security proofs
- [Spec-Rust Linkage](SPEC_RUST_LINKAGE.md) - Type/operation mapping between layers
- [FFI Integration](FFI_INTEGRATION.md) - OCaml extraction ↔ Rust UBT bridge

## Module Hierarchy

| Namespace | Path | Purpose |
|-----------|------|---------|
| `UBT.Specs` | `specs/` | Mathematical specifications |
| `UBT.Sim` | `simulations/` | Idiomatic Rocq implementation (includes security.v) |
| `UBT.Proofs` | `proofs/` | Formal proofs + QuickChick tests |
| `UBT.Linking` | `linking/` | Translation-simulation bridge |
| `src` | `src/` | Auto-generated translation (not part of proof base) |

> **Note:** The `src/` directory contains auto-generated Rocq code from rocq-of-rust. These files are machine-generated from the Rust implementation and are not manually written proofs. The proof base consists of `specs/`, `simulations/`, `proofs/`, and `linking/`.

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total axioms | **67** |
| Parameters | **26** |
| Admitted proofs | **0** ✅ (all closed) |
| QuickChick properties | 5 (10k tests each, 50k total, all passing) |
| OCaml extraction tests | 10/10 passing |
| Security theorems | 30+ (game-based proofs in security.v) |
| FFI bridge | ✅ Created (Rust ↔ OCaml) |

## Key Theorems

### Core Correctness

| Theorem | Location | Statement |
|---------|----------|-----------|
| `get_empty` | tree.v | `sim_tree_get empty_tree k = None` |
| `get_insert_same` | tree.v | Insert then get returns inserted value |
| `get_insert_other_stem` | tree.v | Insert doesn't affect other stems |
| `get_delete` | tree.v | Delete makes key return None |
| `insert_preserves_wf` | tree.v | Well-formedness is preserved |

### Co-location (EIP-7864)

| Theorem | Location | Statement |
|---------|----------|-----------|
| `account_data_same_stem` | embedding_spec.v | Basic data and code hash share stem |
| `header_storage_same_stem` | embedding_spec.v | First 64 slots share account stem |
| `code_chunks_same_group_stem` | embedding_spec.v | Nearby code chunks share stem |

### Merkle Proofs

| Theorem | Location | Statement |
|---------|----------|-----------|
| `inclusion_proof_soundness` | tree.v | Valid proof ⟹ key-value exists |
| `inclusion_proof_completeness` | tree.v | Value exists ⟹ proof exists |
| `exclusion_completeness` | tree.v | Key absent ⟹ exclusion proof exists |

## Build Targets

| Target | Description |
|--------|-------------|
| `make all` | Build specs, simulations, proofs |
| `make translation` | Build translated Rust code |
| `make linking` | Build linking layer |
| `make docs` | Generate HTML documentation |
| `make docs-clean` | Remove generated documentation |
| `make clean` | Remove all build artifacts |
| `make check-deps` | Verify Rocq and RocqOfRust are installed |

## Prerequisites

- **Rocq 9.x** - Install via opam: `opam switch create rocq-9 ocaml.5.2.1`
- **RocqOfRust library** - Required for `make translation` and `make linking`
- **coqdoc** - Included with Rocq, used for `make docs`

## References

- [EIP-7864 Specification](https://eips.ethereum.org/EIPS/eip-7864)
- [rocq-of-rust Documentation](https://github.com/formal-land/rocq-of-rust)
- [Rocq Reference Manual](https://rocq-prover.org/doc/)
- [Verkle Trees Paper](https://verkle.info/)
