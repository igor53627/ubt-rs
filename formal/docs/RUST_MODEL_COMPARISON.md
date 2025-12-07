# Rust Implementation vs. Coq Model Comparison

This document compares the Rust implementation with the Coq simulation model, highlighting key differences and the linking strategy.

## Overview

| Aspect | Rust Implementation | Coq Simulation |
|--------|---------------------|----------------|
| Language | Imperative, mutable | Pure functional |
| Memory | HashMap-based | Inductive types |
| Effects | Side effects | Pure functions |
| Error handling | Result/Option | Option type |

## Type Correspondence

### Core Types

| Rust Type | Coq Type | Location |
|-----------|----------|----------|
| `TreeKey` (32 bytes) | `TreeKey` (list Z, length 32) | `simulations/tree.v` |
| `Value` (32 bytes) | `Value` (list Z, length 32) | `simulations/tree.v` |
| `Stem` (31 bytes) | `Stem` (list Z, length 31) | `simulations/tree.v` |
| `UnifiedBinaryTree<H>` | `SimTree` | `simulations/tree.v` |
| `Node<H>` | `SimNode` | `simulations/tree.v` |
| `B256` | `Bytes32` | `simulations/crypto.v` |

### Node Representation

**Rust (`src/node.rs`):**
```rust
pub enum Node<H: Hasher> {
    Empty,
    Stem(StemNode<H>),
    Internal(InternalNode<H>),
}

pub struct StemNode<H: Hasher> {
    stem: Stem,
    values: HashMap<u8, Value>,
    _hasher: PhantomData<H>,
}
```

**Coq (`simulations/tree.v`):**
```coq
Inductive SimNode : Type :=
  | SimEmpty : SimNode
  | SimStem : Stem -> (Z -> option Value) -> SimNode
  | SimInternal : SimNode -> SimNode -> SimNode.
```

### Key Differences

1. **HashMap vs. Function**: Rust uses `HashMap<u8, Value>` for stem values; Coq uses `Z -> option Value`
2. **Hasher parameter**: Rust is generic over hasher; Coq uses abstract `hash_*` functions
3. **Mutability**: Rust mutates in-place; Coq returns new trees

## Operation Correspondence

| Rust Method | Coq Function | Axiom Linking |
|-------------|--------------|---------------|
| `UnifiedBinaryTree::new()` | `empty_tree` | `NewLink.new_executes` |
| `UnifiedBinaryTree::get()` | `sim_tree_get` | `GetLink.get_executes` |
| `UnifiedBinaryTree::insert()` | `sim_tree_insert` | `InsertLink.insert_executes` |
| `UnifiedBinaryTree::delete()` | `sim_tree_delete` | `DeleteLink.delete_executes` |
| `UnifiedBinaryTree::root_hash()` | `sim_root_hash` | `HashLink.root_hash_executes` |

## Abstraction Gaps

### Modeled in Coq

- Core tree operations (get, insert, delete)
- Root hash computation
- Merkle proof generation and verification
- Key derivation (stem, subindex)
- Co-location properties

### Not Modeled in Coq

| Aspect | Reason |
|--------|--------|
| Memory allocation | Abstracted to pure data |
| Iterator implementation | Debugging utility only |
| Error messages | Content not security-relevant |
| Serialization | Separate concern |
| Concurrency | Single-threaded design |

## Linking Strategy

The linking layer (`linking/operations.v`) bridges the translation and simulation:

```
┌─────────────────────────────────────────────────────────────┐
│                    LINKING STRATEGY                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Rust Code                                                  │
│      │                                                      │
│      │ rocq-of-rust                                         │
│      ▼                                                      │
│  Translation (src/*.v)                                      │
│      │                                                      │
│      │ *_executes axioms (linking/operations.v)             │
│      ▼                                                      │
│  Simulation (simulations/tree.v)                            │
│      │                                                      │
│      │ Proven theorems (proofs/correctness.v)               │
│      ▼                                                      │
│  Specification (specs/tree_spec.v)                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Execution Axioms

Each linking axiom states that running the translated Rust code produces the same result as the simulation:

```coq
Axiom get_executes : forall (sim_t : SimTree) (k : TreeKey),
  (* Running translated Rust get on state corresponding to sim_t *)
  run_get (to_rust_state sim_t) k = 
  (* Produces result matching simulation *)
  to_rust_result (sim_tree_get sim_t k).
```

### Validation

- **QuickChick**: 5 properties, 50,000 tests validate simulation behavior
- **OCaml extraction**: 10/10 tests validate extracted code matches simulation
- **FFI bridge**: Rust ↔ OCaml integration validates end-to-end

## Hash Function Abstraction

| Rust | Coq | Notes |
|------|-----|-------|
| `PoseidonHasher::hash_single()` | `hash_value` | Parameter |
| `PoseidonHasher::hash_pair()` | `hash_pair` | Parameter |
| `PoseidonHasher::hash_stem()` | `hash_stem` | Parameter |

Cryptographic properties (collision resistance, preimage resistance) are axiomatized as they cannot be proven within type theory.

## References

- [SPEC_RUST_LINKAGE.md](SPEC_RUST_LINKAGE.md) - Detailed spec-to-Rust mapping
- [Axiom Audit](axiom_audit.md) - Complete axiom inventory
- [Verification Scope](VERIFICATION_SCOPE.md) - What is and isn't verified
