# UBT Formal Verification - Theorem Reference

This document provides spec-level documentation for all major theorems in the UBT formal verification, with cross-references to source files and explanations of what each theorem proves.

**Last Updated:** December 2025  
**Status:** **VERIFICATION COMPLETE** - 0 admits in simulations, proofs, linking (for current axiom counts run `scripts/count_axioms.sh`)

---

## Abstract Model

The formal verification uses an abstraction function `sim_tree_get` that defines the abstract map semantics:

```text
sim_tree_get : SimTree → TreeKey → option Value
```

**User Mental Model:** A UBT should be thought of as a map from 32-byte keys to 32-byte values, where:
- Keys are split into a 31-byte **stem** and 1-byte **subindex**
- Keys sharing the same stem are co-located in a 256-slot subtree
- The tree is **sparse**: absent keys return `None`. A zero value is a present value: `get` returns `Some zero32` for it. A delete is a separate removal

The `SimTree` type in [simulations/tree.v:L575-577](../simulations/tree.v#L575-L577) models this as a `StemMap` (map from stems to `SubIndexMap`), where each `SubIndexMap` is a map from subindex to value.

---

## Tree Operations

### Get from Empty
- **Theorem:** `get_empty` in [tree.v:L621-627](../simulations/tree.v#L621-L627)
- **Statement:** "Getting any key from an empty tree returns None"
- **Formal:** `∀ k, sim_tree_get empty_tree k = None`
- **Axioms:** None (fully proven)
- **User implication:** Fresh trees contain no data

### Get-Insert Same Key
- **Theorem:** `get_insert_same` in [tree.v:L629-639](../simulations/tree.v#L629-L639)
- **Statement:** "After inserting (k, v), getting k returns v (for every v, including zero)"
- **Formal:** `∀ t k v, sim_tree_get (sim_tree_insert t k v) k = Some v`
- **Axioms:** None (fully proven)
- **User implication:** Inserted values are retrievable

### Get-Insert Other Stem
- **Theorem:** `get_insert_other_stem` in [tree.v:L677-686](../simulations/tree.v#L677-L686)
- **Statement:** "Insert at k₁ doesn't affect get at k₂ when stems differ"
- **Formal:** `∀ t k₁ k₂ v, stem_eq k₁.stem k₂.stem = false → sim_tree_get (insert t k₁ v) k₂ = sim_tree_get t k₂`
- **Axioms:** None (fully proven)
- **User implication:** Keys with different stems are isolated

### Get-Insert Other Subindex
- **Theorem:** `get_insert_other_subindex` in [tree.v:L711-739](../simulations/tree.v#L711-L739)
- **Statement:** "Insert at k₁ doesn't affect get at k₂ when same stem but different subindex"
- **Formal:** `∀ t k₁ k₂ v, stem_eq k₁.stem k₂.stem = true → k₁.subindex ≠ k₂.subindex → sim_tree_get (insert t k₁ v) k₂ = sim_tree_get t k₂`
- **Axioms:** None (fully proven)
- **User implication:** Co-located keys with different subindices don't interfere

### Delete Removes Value
- **Theorem:** `get_delete` in [tree.v:L741-753](../simulations/tree.v#L741-L753)
- **Statement:** "After deleting k, getting k returns None"
- **Formal:** `∀ t k, sim_tree_get (sim_tree_delete t k) k = None`
- **Axioms:** None (fully proven)
- **User implication:** Deleted keys are no longer in the tree. `sim_tree_delete` is a real removal: it removes the subindex, and the stem when it has no entries left (`delete_last_value_removes_stem`). Other keys do not change (`get_delete_other_stem`, `get_delete_other_subindex`), and well-formedness is preserved (`delete_preserves_wf`)

### Zero Insert Is Not a Delete
- **Theorem:** `insert_zero_not_delete` in [tree.v:L813-825](../simulations/tree.v#L813-L825)
- **Statement:** "An insert of zero leaves a present zero leaf; a delete leaves no leaf"
- **Formal:** `∀ t k, sim_tree_get (sim_tree_insert t k zero32) k = Some zero32 ∧ sim_tree_get (sim_tree_delete t k) k = None`
- **Axioms:** None (fully proven)
- **User implication:** A write of zero (the go-ethereum way to delete) and `delete` give different trees

### Order Independence (Different Stems)
- **Theorem:** `insert_order_independent_stems` in [tree.v:L834-983](../simulations/tree.v#L834-L983)
- **Statement:** "Insertion order doesn't matter for different stems"
- **Formal:** `∀ t k₁ v₁ k₂ v₂, stem_eq k₁.stem k₂.stem = false → tree_eq (insert (insert t k₁ v₁) k₂ v₂) (insert (insert t k₂ v₂) k₁ v₁)`
- **Status:** **Fully proven** (December 2025)
- **User implication:** Batch updates can be applied in any order

### Order Independence (Same Stem)
- **Theorem:** `insert_order_independent_subindex` in [tree.v:L1034-1081](../simulations/tree.v#L1034-L1081)
- **Statement:** "Insertion order doesn't matter for same stem, different subindex"
- **Status:** **Fully proven** (December 2025)
- **User implication:** Same as above, for co-located keys

---

## Hash Properties

### Empty Tree Hash
- **Theorem:** `empty_tree_hash_zero` in [tree.v:L1108-1112](../simulations/tree.v#L1108-L1112)
- **Statement:** "Empty tree has zero root hash"
- **Formal:** `sim_node_hash SimEmpty = zero32`
- **Axioms:** None (fully proven)
- **User implication:** Empty state has canonical hash (32 zero bytes)

### Hash Determinism
- **Theorem:** `hash_deterministic_node` in [tree.v:L1115-1119](../simulations/tree.v#L1115-L1119)
- **Statement:** "Same tree always produces same hash"
- **Axioms:** None (proven by reflexivity)
- **User implication:** Hash computation is repeatable

---

## Stem Co-location

### Co-location Theorem
- **Theorem:** `stem_colocation` in [tree.v:L1124-1141](../simulations/tree.v#L1124-L1141)
- **Statement:** "Keys with same stem are stored in same subtree"
- **Formal:** `∀ t k₁ k₂, stem_eq k₁.stem k₂.stem = true → ∃ submap, stems_get (insert t k₁ v).stems k₁.stem = Some submap ∧ stems_get (insert t k₁ v).stems k₂.stem = Some submap`
- **Axioms:** None (fully proven)
- **User implication:** Account data shares Merkle path prefix (EIP-7864 efficiency guarantee)

---

## Well-Formedness

### Insertion Preserves Well-Formedness
- **Theorem:** `insert_preserves_wf` in [tree.v:L1408-1413](../simulations/tree.v#L1408-L1413)
- **Statement:** "Insertion preserves tree well-formedness"
- **Formal:** `∀ t k v, wf_tree t → wf_value v → wf_stem k.stem → wf_tree (sim_tree_insert t k v)`
- **Axioms:** None (fully proven)
- **User implication:** Valid inputs always produce valid trees

---

## Axioms Summary

### Cryptographic Axioms (Low Risk - Standard Assumptions)
| Axiom | File | Line | Purpose |
|-------|------|------|---------|
| `hash_zero_pair` | tree.v | L366 | Zero pair hashes to zero. It is the only zero rule: `hash_zero_value` is removed, and a leaf that holds zero is hashed |
| `hash_deterministic_value` | tree.v | L368-369 | Hash is deterministic (now a lemma, proven) |
| `hash_deterministic_pair` | tree.v | L371-373 | Pair hash is deterministic (now a lemma, proven) |

### Hash Function Parameters (Abstract)
| Parameter | File | Line | Purpose |
|-----------|------|------|---------|
| `hash_value` | tree.v | L355 | Hash a value to 32 bytes |
| `hash_pair` | tree.v | L356 | Hash a pair of 32-byte values |
| `hash_stem` | tree.v | L357 | Hash a stem with subtree hash |

See [axiom_audit.md](axiom_audit.md) for complete axiom documentation.

---

## Verification Status Legend

- **Fully proven**: No axioms beyond standard crypto assumptions
- (!) **Admitted**: Contains `Admitted` - proof incomplete
- [LOCK] **Axiomatized**: Relies on crypto assumptions (appropriate)

For detailed status, see [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md).

---

## Correctness Proofs

The [proofs/correctness.v](../proofs/correctness.v) file re-exports theorems from the simulation layer with additional documentation:

| Theorem | Source | Line |
|---------|--------|------|
| `empty_tree_zero_hash` | correctness.v | L42-46 |
| `hash_deterministic` | correctness.v | L54-58 |
| `get_from_empty` | correctness.v | L65-69 |
| `get_insert_same_key` | correctness.v | L78-83 |
| `zero_write_is_not_delete` | correctness.v | L91-99 |
| `get_insert_different_stem` | correctness.v | L106-112 |
| `get_insert_different_subindex` | correctness.v | L120-127 |
| `get_after_delete` | correctness.v | L137-142 |
| `keys_share_stem_node` | correctness.v | L150-159 |
| `insertion_preserves_wellformedness` | correctness.v | L166-172 |
| `order_independence_different_stems` | correctness.v | L184-192 |

---

## Security Theorems

The [simulations/security.v](../simulations/security.v) file provides game-based security proofs for the UBT Merkle tree construction. These theorems demonstrate that the security of Merkle proofs reduces to the security of the underlying hash function.

### Merkle Path Security

| Theorem | Location | Statement |
|---------|----------|-----------|
| `merkle_path_binding` | [security.v:L46-53](../simulations/security.v#L46-L53) | Same witness path + same root ⟹ same leaf hash |
| `merkle_path_distinct` | [security.v:L62-72](../simulations/security.v#L62-L72) | Different leaves ⟹ different roots (same path) |
| `witness_step_unforgeable` | [security.v:L150-176](../simulations/security.v#L150-L176) | Each Merkle step is unforgeable |
| `witness_non_malleable` | [security.v:L421-493](../simulations/security.v#L421-L493) | Proof tampering is detectable |

### Data Integrity

| Theorem | Location | Statement |
|---------|----------|-----------|
| `value_integrity_from_hash` | [security.v:L82-87](../simulations/security.v#L82-L87) | Hash equality ⟹ value equality |
| `merkle_proof_value_integrity` | [security.v:L99-111](../simulations/security.v#L99-L111) | Same proof path + same root ⟹ same value |
| `end_to_end_proof_security` | [security.v:L308-314](../simulations/security.v#L308-L314) | Verified proof ⟹ value in tree |

### Unforgeability

| Theorem | Location | Statement |
|---------|----------|-----------|
| `internal_node_unforgeability` | [security.v:L121-127](../simulations/security.v#L121-L127) | Same parent hash ⟹ same children |
| `stem_node_unforgeability` | [security.v:L135-142](../simulations/security.v#L135-L142) | Same stem hash ⟹ same stem and subtree |
| `merkle_security_reduction` | [security.v:L213-224](../simulations/security.v#L213-L224) | Forgery ⟹ hash collision |
| `no_forgery_without_collision` | [security.v:L232-244](../simulations/security.v#L232-L244) | Collision resistance ⟹ no forgery |

### Game-Based Security (EUF-MPA)

| Theorem | Location | Statement |
|---------|----------|-----------|
| `euf_mpa_security` | [security.v:L1157-1169](../simulations/security.v#L1157-L1169) | Existential unforgeability under Merkle proof attack |
| `euf_implies_consistency` | [security.v:L1172-1181](../simulations/security.v#L1172-L1181) | EUF-MPA ⟹ consistent oracle state |
| `binding_game_security` | [security.v:L1210-1226](../simulations/security.v#L1210-L1226) | Binding game: no adversary wins |
| `merkle_forgery_advantage_negligible` | [security.v:L1307-1321](../simulations/security.v#L1307-L1321) | Forgery advantage < 2^128 for q < 2^64 |

### Accumulator Security

| Theorem | Location | Statement |
|---------|----------|-----------|
| `accumulator_inclusion_sound` | [security.v:L1252-1262](../simulations/security.v#L1252-L1262) | Cannot prove membership of non-members |
| `accumulator_exclusion_sound` | [security.v:L1265-1275](../simulations/security.v#L1265-L1275) | Cannot prove non-membership of members |
| `accumulator_correctness` | [security.v:L1391-1403](../simulations/security.v#L1391-L1403) | Accumulated elements have valid witnesses |
| `accumulator_membership_soundness` | [security.v:L1411-1420](../simulations/security.v#L1411-L1420) | Verified witness ⟹ element in tree |
| `accumulator_uniqueness` | [security.v:L1440-1455](../simulations/security.v#L1440-L1455) | Each key has at most one value |
| `commitment_is_binding` | [security.v:L1486-1497](../simulations/security.v#L1486-L1497) | Root hash binds to tree contents |

### Consistency Properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `batch_proof_consistency` | [security.v:L323-332](../simulations/security.v#L323-L332) | Batch proofs for same key must agree |
| `history_independence_semantics` | [security.v:L746-754](../simulations/security.v#L746-L754) | Same final state ⟹ same semantics |
| `get_insert_consistency` | [security.v:L953-958](../simulations/security.v#L953-L958) | Get-insert operations are consistent |
| `insert_delete_consistency` | [security.v:L965-971](../simulations/security.v#L965-L971) | Insert-delete operations are consistent |

---

## Iterator Modeling (Low Priority)

The [simulations/iterator.v](../simulations/iterator.v) file provides iterator modeling for completeness. These are **informational/low-priority** specifications since the Rust implementation uses HashMap with arbitrary iteration order.

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
| `keys_complete` | [iterator.v:L179-236](../simulations/iterator.v#L179-L236) | All inserted keys appear in iteration |
| `keys_unique` | [iterator.v:L378-381](../simulations/iterator.v#L378-L381) | No duplicate keys (requires wf_tree) |
| `entries_match_get` | [iterator.v:L450-453](../simulations/iterator.v#L450-L453) | Iterated entries match individual gets |
| `key_in_iff_get_some` | [iterator.v:L578-581](../simulations/iterator.v#L578-L581) | k ∈ keys ⟺ get k = Some v |
| `entry_in_iff_get` | [iterator.v:L606-638](../simulations/iterator.v#L606-L638) | Full characterization of entries |
| `fold_cons_entries` | [iterator.v:L468-480](../simulations/iterator.v#L468-L480) | Fold with cons equals rev(entries) |

### Notes

- **Priority:** Low - provided for completeness only
- **Ordering:** Iterator order is abstract/unspecified (matches HashMap behavior)
- **Admits:** None. `simulations/iterator.v` has no `Admitted` proofs; it declares 4 axioms
- **Use Case:** Reasoning about bulk operations, not performance-critical code

---

## Note on Linking Layer

The definitions and verification functions that the linking layer (`linking/operations.v`) needs are in place (December 2025). The proofs are not complete: they depend on axioms.
- All required types (`sim_root_hash`, `BatchInclusionProof`, `BatchExclusionProof`, `BatchProof`) added to `simulations/tree.v`
- All verification functions (`verify_batch_inclusion`, `verify_batch_exclusion`, `verify_batch_mixed`) implemented
- Proof types (`SharedWitness`, `InclusionProof`, `ExclusionProof`) fully defined
- Soundness statements (`exclusion_proof_soundness`, `inclusion_proof_soundness`) are axioms in `simulations/tree.v`
- The execution statements `get_executes`, `insert_executes`, `new_executes` and `root_hash_executes` are axioms in `linking/operations.v` (lines 372, 488, 707, 779). That file declares 10 axioms, and `formal/linking/` declares 46

**Status:** `make linking` now builds successfully.
