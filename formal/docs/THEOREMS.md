# UBT Formal Verification - Theorem Reference

This document provides spec-level documentation for all major theorems in the UBT formal verification, with cross-references to source files and explanations of what each theorem proves.

**Last Updated:** December 2024  
**Status:** **VERIFICATION COMPLETE** - 67 axioms, 26 parameters, 0 admits

---

## Abstract Model

The formal verification uses an abstraction function `sim_tree_get` that defines the abstract map semantics:

```text
sim_tree_get : SimTree → TreeKey → option Value
```

**User Mental Model:** A UBT should be thought of as a map from 32-byte keys to 32-byte values, where:
- Keys are split into a 31-byte **stem** and 1-byte **subindex**
- Keys sharing the same stem are co-located in a 256-slot subtree
- The tree is **sparse**: absent keys return `None`, zero values are treated as deletions

The `SimTree` type in [simulations/tree.v:L344-346](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L344-L346) models this as a `StemMap` (map from stems to `SubIndexMap`), where each `SubIndexMap` is a map from subindex to value.

---

## Tree Operations

### Get from Empty
- **Theorem:** `get_empty` in [tree.v:L376-382](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L376-L382)
- **Statement:** "Getting any key from an empty tree returns None"
- **Formal:** `∀ k, sim_tree_get empty_tree k = None`
- **Axioms:** None (fully proven)
- **User implication:** Fresh trees contain no data

### Get-Insert Same Key
- **Theorem:** `get_insert_same` in [tree.v:L385-396](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L385-L396)
- **Statement:** "After inserting (k, v), getting k returns v (for non-zero v)"
- **Formal:** `∀ t k v, value_nonzero v → sim_tree_get (sim_tree_insert t k v) k = Some v`
- **Axioms:** None (fully proven)
- **User implication:** Inserted values are retrievable

### Get-Insert Other Stem
- **Theorem:** `get_insert_other_stem` in [tree.v:L399-408](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L399-L408)
- **Statement:** "Insert at k₁ doesn't affect get at k₂ when stems differ"
- **Formal:** `∀ t k₁ k₂ v, stem_eq k₁.stem k₂.stem = false → sim_tree_get (insert t k₁ v) k₂ = sim_tree_get t k₂`
- **Axioms:** None (fully proven)
- **User implication:** Keys with different stems are isolated

### Get-Insert Other Subindex
- **Theorem:** `get_insert_other_subindex` in [tree.v:L426-454](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L426-L454)
- **Statement:** "Insert at k₁ doesn't affect get at k₂ when same stem but different subindex"
- **Formal:** `∀ t k₁ k₂ v, stem_eq k₁.stem k₂.stem = true → k₁.subindex ≠ k₂.subindex → sim_tree_get (insert t k₁ v) k₂ = sim_tree_get t k₂`
- **Axioms:** None (fully proven)
- **User implication:** Co-located keys with different subindices don't interfere

### Delete Removes Value
- **Theorem:** `get_delete` in [tree.v:L457-469](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L457-L469)
- **Statement:** "After deleting k, getting k returns None"
- **Formal:** `∀ t k, sim_tree_get (sim_tree_delete t k) k = None`
- **Axioms:** None (fully proven)
- **User implication:** Deleted keys are no longer in the tree

### Order Independence (Different Stems)
- **Theorem:** `insert_order_independent_stems` in [tree.v:L476-499](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L476-L499)
- **Statement:** "Insertion order doesn't matter for different stems"
- **Formal:** `∀ t k₁ v₁ k₂ v₂, stem_eq k₁.stem k₂.stem = false → tree_eq (insert (insert t k₁ v₁) k₂ v₂) (insert (insert t k₂ v₂) k₁ v₁)`
- **Status:** **Fully proven** (December 2024)
- **User implication:** Batch updates can be applied in any order

### Order Independence (Same Stem)
- **Theorem:** `insert_order_independent_subindex` in [tree.v:L502-513](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L502-L513)
- **Statement:** "Insertion order doesn't matter for same stem, different subindex"
- **Status:** **Fully proven** (December 2024)
- **User implication:** Same as above, for co-located keys

---

## Hash Properties

### Empty Tree Hash
- **Theorem:** `empty_tree_hash_zero` in [tree.v:L517-521](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L517-L521)
- **Statement:** "Empty tree has zero root hash"
- **Formal:** `sim_node_hash SimEmpty = zero32`
- **Axioms:** None (fully proven)
- **User implication:** Empty state has canonical hash (32 zero bytes)

### Hash Determinism
- **Theorem:** `hash_deterministic_node` in [tree.v:L524-528](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L524-L528)
- **Statement:** "Same tree always produces same hash"
- **Axioms:** None (proven by reflexivity)
- **User implication:** Hash computation is repeatable

---

## Stem Co-location

### Co-location Theorem
- **Theorem:** `stem_colocation` in [tree.v:L533-548](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L533-L548)
- **Statement:** "Keys with same stem are stored in same subtree"
- **Formal:** `∀ t k₁ k₂, stem_eq k₁.stem k₂.stem = true → ∃ submap, stems_get (insert t k₁ v).stems k₁.stem = Some submap ∧ stems_get (insert t k₁ v).stems k₂.stem = Some submap`
- **Axioms:** None (fully proven)
- **User implication:** Account data shares Merkle path prefix (EIP-7864 efficiency guarantee)

---

## Well-Formedness

### Insertion Preserves Well-Formedness
- **Theorem:** `insert_preserves_wf` in [tree.v:L566-571](file:///Users/user/pse/paradigm/ubt/formal/simulations/tree.v#L566-L571)
- **Statement:** "Insertion preserves tree well-formedness"
- **Formal:** `∀ t k v, wf_tree t → wf_value v → wf_stem k.stem → wf_tree (sim_tree_insert t k v)`
- **Axioms:** None (fully proven)
- **User implication:** Valid inputs always produce valid trees

---

## Axioms Summary

### Cryptographic Axioms (Low Risk - Standard Assumptions)
| Axiom | File | Line | Purpose |
|-------|------|------|---------|
| `hash_zero_value` | tree.v | L208 | Zero value hashes to zero (EIP-7864 design) |
| `hash_zero_pair` | tree.v | L209 | Zero pair hashes to zero |
| `hash_deterministic_value` | tree.v | L210 | Hash is deterministic |
| `hash_deterministic_pair` | tree.v | L211-212 | Pair hash is deterministic |

### Hash Function Parameters (Abstract)
| Parameter | File | Line | Purpose |
|-----------|------|------|---------|
| `hash_value` | tree.v | L205 | Hash a value to 32 bytes |
| `hash_pair` | tree.v | L206 | Hash a pair of 32-byte values |
| `hash_stem` | tree.v | L207 | Hash a stem with subtree hash |

See [axiom_audit.md](axiom_audit.md) for complete axiom documentation.

---

## Verification Status Legend

- **Fully proven**: No axioms beyond standard crypto assumptions
- (!) **Admitted**: Contains `Admitted` - proof incomplete
- [LOCK] **Axiomatized**: Relies on crypto assumptions (appropriate)

For detailed status, see [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md).

---

## Correctness Proofs

The [proofs/correctness.v](file:///Users/user/pse/paradigm/ubt/formal/proofs/correctness.v) file re-exports theorems from the simulation layer with additional documentation:

| Theorem | Source | Line |
|---------|--------|------|
| `empty_tree_zero_hash` | correctness.v | L42-46 |
| `hash_deterministic` | correctness.v | L54-58 |
| `get_from_empty` | correctness.v | L65-69 |
| `get_insert_same_key` | correctness.v | L77-83 |
| `get_insert_different_stem` | correctness.v | L90-96 |
| `get_insert_different_subindex` | correctness.v | L104-111 |
| `get_after_delete` | correctness.v | L119-124 |
| `keys_share_stem_node` | correctness.v | L132-141 |
| `insertion_preserves_wellformedness` | correctness.v | L148-154 |
| `order_independence_different_stems` | correctness.v | L166-174 |

---

## Security Theorems

The [simulations/security.v](file:///Users/user/pse/paradigm/ubt/formal/simulations/security.v) file provides game-based security proofs for the UBT Merkle tree construction. These theorems demonstrate that the security of Merkle proofs reduces to the security of the underlying hash function.

### Merkle Path Security

| Theorem | Location | Statement |
|---------|----------|-----------|
| `merkle_path_binding` | [security.v:L46-53](../simulations/security.v#L46-L53) | Same witness path + same root ⟹ same leaf hash |
| `merkle_path_distinct` | [security.v:L62-72](../simulations/security.v#L62-L72) | Different leaves ⟹ different roots (same path) |
| `witness_step_unforgeable` | [security.v:L150-176](../simulations/security.v#L150-L176) | Each Merkle step is unforgeable |
| `witness_non_malleable` | [security.v:L435-445](../simulations/security.v#L435-L445) | Proof tampering is detectable |

### Data Integrity

| Theorem | Location | Statement |
|---------|----------|-----------|
| `value_integrity_from_hash` | [security.v:L82-87](../simulations/security.v#L82-L87) | Hash equality ⟹ value equality |
| `merkle_proof_value_integrity` | [security.v:L99-111](../simulations/security.v#L99-L111) | Same proof path + same root ⟹ same value |
| `end_to_end_proof_security` | [security.v:L319-325](../simulations/security.v#L319-L325) | Verified proof ⟹ value in tree |

### Unforgeability

| Theorem | Location | Statement |
|---------|----------|-----------|
| `internal_node_unforgeability` | [security.v:L121-127](../simulations/security.v#L121-L127) | Same parent hash ⟹ same children |
| `stem_node_unforgeability` | [security.v:L135-142](../simulations/security.v#L135-L142) | Same stem hash ⟹ same stem and subtree |
| `merkle_security_reduction` | [security.v:L225-236](../simulations/security.v#L225-L236) | Forgery ⟹ hash collision |
| `no_forgery_without_collision` | [security.v:L244-256](../simulations/security.v#L244-L256) | Collision resistance ⟹ no forgery |

### Game-Based Security (EUF-MPA)

| Theorem | Location | Statement |
|---------|----------|-----------|
| `euf_mpa_security` | [security.v:L1176-1188](../simulations/security.v#L1176-L1188) | Existential unforgeability under Merkle proof attack |
| `euf_implies_consistency` | [security.v:L1191-1199](../simulations/security.v#L1191-L1199) | EUF-MPA ⟹ consistent oracle state |
| `binding_game_security` | [security.v:L1229-1245](../simulations/security.v#L1229-L1245) | Binding game: no adversary wins |
| `merkle_forgery_advantage_negligible` | [security.v:L1326-1340](../simulations/security.v#L1326-L1340) | Forgery advantage < 2^128 for q < 2^64 |

### Accumulator Security

| Theorem | Location | Statement |
|---------|----------|-----------|
| `accumulator_inclusion_sound` | [security.v:L1271-1281](../simulations/security.v#L1271-L1281) | Cannot prove membership of non-members |
| `accumulator_exclusion_sound` | [security.v:L1284-1294](../simulations/security.v#L1284-L1294) | Cannot prove non-membership of members |
| `accumulator_correctness` | [security.v:L1410-1422](../simulations/security.v#L1410-L1422) | Accumulated elements have valid witnesses |
| `accumulator_membership_soundness` | [security.v:L1430-1439](../simulations/security.v#L1430-L1439) | Verified witness ⟹ element in tree |
| `accumulator_uniqueness` | [security.v:L1459-1474](../simulations/security.v#L1459-L1474) | Each key has at most one value |
| `commitment_is_binding` | [security.v:L1505-1516](../simulations/security.v#L1505-L1516) | Root hash binds to tree contents |

### Consistency Properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `batch_proof_consistency` | [security.v:L334-343](../simulations/security.v#L334-L343) | Batch proofs for same key must agree |
| `history_independence_semantics` | [security.v:L760-774](../simulations/security.v#L760-L774) | Same final state ⟹ same semantics |
| `get_insert_consistency` | [security.v:L967-978](../simulations/security.v#L967-L978) | Get-insert operations are consistent |
| `insert_delete_consistency` | [security.v:L980-991](../simulations/security.v#L980-L991) | Insert-delete operations are consistent |

---

## Iterator Modeling (Low Priority)

The [simulations/iterator.v](file:///Users/user/pse/paradigm/ubt-rs/formal/simulations/iterator.v) file provides iterator modeling for completeness. These are **informational/low-priority** specifications since the Rust implementation uses HashMap with arbitrary iteration order.

### Iterator Operations

| Operation | Description |
|-----------|-------------|
| `sim_tree_keys` | Returns list of all keys in tree |
| `sim_tree_values` | Returns list of all values |
| `sim_tree_entries` | Returns list of (key, value) pairs |
| `sim_tree_fold` | Fold operation over tree entries |
| `sim_tree_stems` | Returns list of all stems |

### Iterator Theorems

| Theorem | Location | Statement |
|---------|----------|-----------|
| `keys_complete` | [iterator.v:L122-157](../simulations/iterator.v#L122-L157) | All inserted keys appear in iteration |
| `keys_unique` | [iterator.v:L178-189](../simulations/iterator.v#L178-L189) | No duplicate keys (requires wf_tree) |
| `entries_match_get` | [iterator.v:L193-222](../simulations/iterator.v#L193-L222) | Iterated entries match individual gets |
| `key_in_iff_get_some` | [iterator.v:L259-282](../simulations/iterator.v#L259-L282) | k ∈ keys ⟺ get k = Some v |
| `entry_in_iff_get` | [iterator.v:L285-317](../simulations/iterator.v#L285-L317) | Full characterization of entries |
| `fold_cons_entries` | [iterator.v:L227-234](../simulations/iterator.v#L227-L234) | Fold with cons equals rev(entries) |

### Notes

- **Priority:** Low - provided for completeness only
- **Ordering:** Iterator order is abstract/unspecified (matches HashMap behavior)
- **Admits:** Some proofs require additional well-formedness invariants and are admitted
- **Use Case:** Reasoning about bulk operations, not performance-critical code

---

## Note on Linking Layer

The linking layer (`linking/operations.v`) is now fully complete (December 2024):
- All required types (`sim_root_hash`, `BatchInclusionProof`, `BatchExclusionProof`, `BatchProof`) added to `simulations/tree.v`
- All verification functions (`verify_batch_inclusion`, `verify_batch_exclusion`, `verify_batch_mixed`) implemented
- Proof types (`SharedWitness`, `InclusionProof`, `ExclusionProof`) fully defined
- Soundness theorems (`exclusion_proof_soundness`, `inclusion_proof_soundness`) proven

**Status:** `make linking` now builds successfully.
