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
| `Node` | `SimNode` | `simulations/tree.v` |
| `B256` | `Bytes32` | `simulations/crypto.v` |

### Node Representation

**Rust (`src/node.rs`):**
```rust
pub enum Node {
    Empty,
    Internal(InternalNode),
    Stem(StemNode),
    Leaf(LeafNode),
}

pub struct StemNode {
    pub stem: Stem,
    pub values: HashMap<SubIndex, B256>,
}
```

**Coq (`simulations/tree.v`):**
```coq
Inductive SimNode : Type :=
  | SimEmpty : SimNode
  | SimInternal : SimNode -> SimNode -> SimNode
  | SimStem : Stem -> SubIndexMap -> SimNode
  | SimLeaf : Value -> SimNode.
```

### Key Differences

1. **HashMap vs. association list**: Rust uses `HashMap<SubIndex, B256>` for stem values; Coq uses `SubIndexMap := list (SubIndex * Value)`
2. **Hasher parameter**: The Rust tree is generic over the hasher (`UnifiedBinaryTree<H, S>`; the node types are not generic); Coq uses abstract `hash_*` functions
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

```text
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

- **QuickChick**: 22 CI properties, 11,000 tests validate simulation behavior
- **OCaml extraction**: 10/10 tests validate extracted code matches simulation
- **FFI bridge**: Rust ↔ OCaml integration validates end-to-end

## Hash Function Abstraction

| Rust | Coq | Notes |
|------|-----|-------|
| `Hasher::hash_32()` | `hash_value` | Parameter |
| `Hasher::hash_64()` | `hash_pair` | Parameter |
| `Hasher::hash_stem_node()` | `hash_stem` | Parameter |

Cryptographic properties (collision resistance, preimage resistance) are axiomatized as they cannot be proven within type theory.

## References

- [SPEC_RUST_LINKAGE.md](SPEC_RUST_LINKAGE.md) - Detailed spec-to-Rust mapping
- [Axiom Audit](axiom_audit.md) - Complete axiom inventory
- [Verification Scope](VERIFICATION_SCOPE.md) - What is and isn't verified
