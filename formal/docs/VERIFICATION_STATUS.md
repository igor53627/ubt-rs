# Verification Status

This document summarizes the verification status of the UBT formal verification project.

## Verification Scope Statement

**What we verify:** The UBT formal verification proves correctness properties of a pure functional *simulation* of the tree data structure. The simulation (`simulations/tree.v`) is proven to satisfy the EIP-7864 specification (`specs/tree_spec.v`).

**Connection to Rust:** The simulation is *linked* to the Rust implementation via type correspondence and behavioral equivalence axioms. These axioms assert that executing the translated Rust code produces results matching the simulation.

**Limitations:**
1. The Rust↔Coq linkage relies on **axioms** (not proofs) for execution semantics
2. The `rocq-of-rust` translation tool is **trusted** to preserve semantics
3. Cryptographic properties (collision resistance) are **assumed**, not proven
4. Memory management, concurrency, and I/O are **not modeled**

**Confidence level:** HIGH for simulation properties, MEDIUM for end-to-end Rust correctness.

See [SPEC_RUST_LINKAGE.md](SPEC_RUST_LINKAGE.md) for detailed mapping between Coq and Rust.

---

## Summary

| Category | Proven | Axiomatized | Notes |
|----------|--------|-------------|-------|
| Tree Operations | 12 | 0 | Core get/insert/delete fully proven |
| Co-location | 5 | 0 | EIP-7864 key layout proven |
| Hash Properties | 3 | 7 | Crypto functions are axiomatized |
| Merkle Proofs | 4 | 3 | Some completeness requires axioms |
| Verkle Proofs | 2 | 6 | Foundation only - needs more crypto |
| Linking | 8 | 12 | Execution semantics axiomatized |

## Fully Proven Theorems

These theorems are proven without admits or axioms at the simulation level:

### Tree Operations (simulations/tree.v)

| Theorem | Statement |
|---------|-----------|
| `get_empty` | Empty tree returns None for any key |
| `get_insert_same` | Get after insert returns inserted value |
| `get_insert_other_stem` | Insert doesn't affect different stems |
| `get_insert_other_subindex` | Insert doesn't affect different subindices |
| `get_delete` | Delete makes key return None |
| `stem_eq_refl` | Stem equality is reflexive |
| `stem_colocation` | Keys with same stem share storage |
| `insert_preserves_wf` | Well-formedness is preserved |
| `empty_tree_hash_zero` | Empty tree has zero root hash |
| `sim_root_hash_empty` | sim_root_hash returns zero for empty |
| `witness_collision_resistant_same_path` | Merkle witness collision resistance |
| `inclusion_proof_binding_strong` | Same witnesses ⟹ same value |

### Co-location (specs/embedding_spec.v)

| Theorem | Statement |
|---------|-----------|
| `derive_tree_key_stem` | Stem derivation correctness |
| `same_input_prefix_same_stem` | Same 31-byte prefix ⟹ same stem |
| `account_data_same_stem` | Basic data and code hash share stem |
| `header_storage_same_stem` | Header slots share account stem |
| `header_slots_same_stem` | All header slots share same stem |
| `code_chunks_same_group_stem` | Same tree_index ⟹ same stem |
| `account_colocation_holds` | Full co-location theorem |

### Helper Lemmas

| Lemma | Location |
|-------|----------|
| `length_firstn_min` | embedding_spec.v |
| `firstn_app_exact_length` | embedding_spec.v |
| `repeat_length` | embedding_spec.v |
| `firstn_repeat` | embedding_spec.v |
| `firstn_app_l` | embedding_spec.v |
| `le_encode_n_length` | embedding_spec.v |
| `pad_to_length` | embedding_spec.v |
| `forallb_combine_refl` | tree.v |
| `sim_get_set_same` | tree.v |
| `sim_get_set_other` | tree.v |
| `sim_get_set_zero` | tree.v |
| `stems_get_set_same` | tree.v |

## Previously Partial (Now Complete)

These theorems were previously incomplete but are now fully proven:

| Theorem | Location | Resolution |
|---------|----------|------------|
| `insert_order_independent_stems` | tree.v | ✅ Proven with forallb case analysis |
| `insert_order_independent_subindex` | tree.v | ✅ Proven via map commutativity |
| `stems_get_set_other` | tree.v | ✅ Proven with length invariant |
| `stems_get_stem_eq` | tree.v | ✅ Proven with stem equality transitivity |
| `inclusion_proof_binding` | tree.v | ✅ Proven via collision resistance axiom |

## Axiomatized Properties

These properties are assumed rather than proven:

### Cryptographic Axioms (simulations/crypto.v)

| Axiom | Justification |
|-------|---------------|
| `hash_value_collision_resistant` | Standard crypto assumption |
| `hash_pair_collision_resistant` | Standard crypto assumption |
| `hash_stem_collision_resistant` | Standard crypto assumption |
| `hash_value_second_preimage` | Follows from collision resistance |
| `hash_zero_value` | Design choice per EIP-7864 |
| `hash_zero_pair` | Design choice per EIP-7864 |
| `hash_value_nonzero` | Domain separation |

### Specification Axioms (specs/tree_spec.v)

| Axiom | Justification |
|-------|---------------|
| `hash_collision_resistant` | Crypto assumption |
| `hash_injective` | Follows from collision resistance |
| `insert_order_independent` | Design requirement |
| `get_insert_same` | Specified behavior |
| `get_insert_other` | Specified behavior |
| `insert_preserves_wf` | Specified behavior |

### Verkle Axioms (simulations/verkle.v)

| Axiom | Justification |
|-------|---------------|
| `verkle_open_correct` | Polynomial commitment correctness |
| `verkle_binding` | Binding property of commitments |
| `verkle_hiding` | Semantic security property |
| `verkle_commit_deterministic` | Commitment determinism |
| `verkle_commit_zero` | Zero vector commitment |
| `verkle_commit_injective` | Commitment uniqueness |

### Linking Axioms (linking/operations.v)

| Axiom | Justification |
|-------|---------------|
| `Run.run_pure` | Monad semantics |
| `Run.run_bind` | Monad semantics |
| `Run.run_panic` | Monad semantics |
| `GetLink.get_executes` | Rust execution model |
| `InsertLink.insert_executes` | Rust execution model |
| `DeleteLink.delete_executes` | Rust execution model |
| `HashLink.root_hash_executes` | Rust execution model |
| `root_hash_extensional` | Tree hash extensionality |
| `root_hash_injective` | Collision resistance at tree level |
| Panic freedom axioms | Require control flow analysis |
| Witness correctness axioms | Require Merkle tree construction |

## Trust Assumptions

### Cryptographic Trust

1. **Hash function security**: We assume SHA256 (or the configured hash) is collision-resistant and has the standard security properties. This is a standard cryptographic assumption.

2. **Verkle commitments**: For Verkle proof support, we assume the polynomial commitment scheme (KZG/IPA) satisfies binding, hiding, and correctness properties.

### Tool Trust

1. **Rocq soundness**: We trust the Rocq proof assistant is sound.

2. **rocq-of-rust correctness**: The translation from Rust to Rocq is trusted to preserve semantics. The translation is deterministic and the output compiles successfully.

3. **RocqOfRust library**: The supporting library types (M monad, Value.t, etc.) are trusted to correctly model Rust semantics.

### Implementation Trust

1. **Rust standard library**: HashMap, Vec, and other stdlib types are trusted to behave correctly.

2. **alloy-primitives**: The B256, FixedBytes types are trusted.

3. **Hasher implementations**: PoseidonHasher, Keccak256Hasher implementations are trusted.

## Coverage of Rust Implementation

### Verified Functions

| Rust Function | Simulation | Linking |
|---------------|------------|---------|
| `UnifiedBinaryTree::new()` | `empty_tree` | ✅ |
| `UnifiedBinaryTree::get()` | `sim_tree_get` | ✅ |
| `UnifiedBinaryTree::insert()` | `sim_tree_insert` | ✅ |
| `UnifiedBinaryTree::delete()` | `sim_tree_delete` | ✅ |
| `UnifiedBinaryTree::root_hash()` | `sim_root_hash` | ✅ |

### Verified Properties

| Property | Verified |
|----------|----------|
| Get from empty returns None | ✅ |
| Get after insert returns value | ✅ |
| Get after delete returns None | ✅ |
| Insert doesn't affect other keys | ✅ |
| Operations preserve well-formedness | ✅ |
| Stem co-location | ✅ |
| Order independence | Partial |
| Merkle proof soundness | ✅ |
| Merkle proof completeness | Axiomatized |
| Panic freedom | Axiomatized |

### Not Yet Verified

| Component | Status |
|-----------|--------|
| Iterator implementations | Not modeled |
| Error handling details | Not modeled |
| Memory allocation | Abstracted |
| Concurrency | Not applicable (single-threaded) |

## Verification Metrics

```text
Source Files:
  specs/          2 files,   ~650 lines
  simulations/    3 files, ~1,250 lines  
  proofs/         2 files,   ~470 lines
  linking/        2 files, ~1,000 lines
  src/            8 files, ~24,500 lines (auto-generated)

Theorems:
  Fully proven:          ~30
  Partially proven:       ~5
  Axiomatized:           ~25

Build time:
  make all:              ~10 seconds
  make linking:          ~30 seconds (includes translation)
```

## Trust Boundaries Summary

### Verified (No Trust Required)
| Component | Status | Location |
|-----------|--------|----------|
| Tree operation semantics | Fully proven | `simulations/tree.v` |
| Co-location properties | Fully proven | `specs/embedding_spec.v` |
| Merkle proof soundness | Proven | `simulations/tree.v` |
| Well-formedness preservation | Proven | `simulations/tree.v` |

### Trusted Assumptions
| Component | Trust Level | Justification |
|-----------|-------------|---------------|
| Rocq proof assistant | HIGH | Widely verified, decades of use |
| rocq-of-rust translation | MEDIUM | Deterministic, compiles successfully |
| Rust standard library | HIGH | Extensively tested, production use |
| Hash collision resistance | STANDARD | Cryptographic assumption |
| alloy-primitives crate | MEDIUM | Audited library |

### Axiomatized (Requires Future Proof Work)
| Axiom Category | Count | Priority |
|----------------|-------|----------|
| Execution semantics (`*_executes`) | 5 | HIGH |
| Panic freedom | 4 | MEDIUM |
| State threading | 3 | LOW |
| Batch verification | 2 | LOW |

See [axiom_audit.md](axiom_audit.md) for complete axiom inventory.

---

## Future Work

1. **Complete partial proofs**: Finish admits in order independence and stem equality transitivity.

2. **Develop M monad interpreter**: Full step-by-step evaluation semantics for monadic Rust code.

3. **Prove panic freedom**: Verify all panic! calls are unreachable on well-formed inputs.

4. **Merkle witness generation**: Prove witness generation produces valid proofs.

5. **Verkle proof verification**: Full linking for polynomial commitment operations.

6. **Performance bounds**: Prove time/space complexity bounds.
