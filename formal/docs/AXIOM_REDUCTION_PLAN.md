# Axiom Reduction Plan

This document catalogs all 67 axioms in the UBT formal verification codebase,
categorizes them by reducibility, and provides a prioritized plan for conversion.

## Summary

| Category    | Count | Description                                    |
|-------------|-------|------------------------------------------------|
| FUNDAMENTAL | 26    | Cryptographic assumptions, cannot be proven    |
| DERIVABLE   | 8     | Can be derived from existing axioms/lemmas     |
| PROVABLE    | 35    | Can be proven with additional work             |
| REDUNDANT   | 15    | Duplicates or can be eliminated                |
| CONVERTED   | 16    | Admitted proofs converted to tagged axioms     |
| INTERFACE   | 31    | External contract specs (serialization, encoding) |
| DESIGN      | 3     | Security design requirements                   |
| **Total**   | **122**|                                               |

### New Axioms Added (40 total)
- **serialization.v**: 22 axioms (28 INTERFACE, 3 DESIGN)
- **interpreter.v**: 18 axioms (3 INTERFACE, 5 FUNDAMENTAL, 10 PROVABLE)

### Conversion Progress
- ✅ `insert_order_independent_subindex` (tree.v) - Converted to lemma using `sim_set_comm`
- ✅ 15 `Admitted` proofs converted to properly tagged `Axiom` declarations:
  - **iterator.v (4)**: `keys_unique_axiom`, `entries_match_get_axiom`, `entry_count_sum_axiom`, `key_in_iff_get_some_axiom`
  - **complexity.v (6)**: `tree_proof_size_bound_axiom`, `proof_size_logarithmic_axiom`, `stem_colocation_shared_tree_proof_axiom`, `stem_colocation_reduces_proofs_axiom`, `multiproof_shared_stem_efficiency_axiom`, `multiproof_more_efficient_axiom`
  - **verkle_linking.v (5)**: `pairing_bilinear_sym_axiom`, `verkle_binding_from_kzg_axiom`, `multi_open_from_singles_axiom`, `aggregation_preserves_binding_axiom`, `IPA_binding_equivalent_to_KZG_axiom`

---

## Category: FUNDAMENTAL (18 axioms)

These axioms represent cryptographic or external assumptions that cannot be proven
within the type theory. They form the trusted base.

### Crypto Core (6 axioms)
| Axiom | File | Reason |
|-------|------|--------|
| `hash_value_collision_resistant` | crypto.v:165 | Rogaway-Shrimpton CR assumption |
| `hash_pair_collision_resistant` | crypto.v:169 | CR for Merkle internal nodes |
| `hash_stem_collision_resistant` | crypto.v:173 | CR for stem hashing |
| `verkle_binding` | verkle.v:55 | Polynomial commitment binding property |
| `verkle_open_correct` | verkle.v:46 | PC opening correctness |
| `verkle_commit_injective` | verkle.v:79 | PC injectivity (follows from binding) |

### Group/Pairing (5 axioms)
| Axiom | File | Reason |
|-------|------|--------|
| `G_add_assoc`, `G_add_comm`, `G_add_identity`, `G_add_inverse` | verkle_linking.v:73-76 | Elliptic curve group axioms |
| `pairing_bilinear` | verkle_linking.v:96 | Bilinearity for KZG |
| `pairing_nondegen` | verkle_linking.v:109 | Non-degeneracy |

### Execution Semantics (7 axioms)
| Axiom | File | Reason |
|-------|------|--------|
| `get_executes` | operations.v:349 | M monad semantics - needs interpreter |
| `insert_executes` | operations.v:407 | M monad semantics |
| `delete_executes` | operations.v:479 | M monad semantics |
| `Run.run_pure` | operations.v:205 | M monad law |
| `Run.run_bind` | operations.v:210 | M monad sequencing |
| `Run.run_panic` | operations.v:224 | Panic semantics |
| `Run.run_eval_sound` | operations.v:231 | Step semantics connection |

---

## Category: DERIVABLE (8 axioms)

These can be derived from other axioms or proven lemmas with straightforward proofs.

### 1. `stem_eq_true` (tree.v:178) → CONVERTED TO LEMMA
**Status**: Already has proven version `stem_eq_true_wf`
**Derivation**: Use `stem_eq_true_wf` with global `wf_stem` invariant
**Effort**: 5 min (add wf_stem precondition threading)

### 2. `stem_eq_via_third` (tree.v:444) → CONVERTED TO LEMMA
**Status**: Already has proven version `stem_eq_trans`
**Derivation**: Use `stem_eq_trans` with length preconditions from `wf_stem`
**Effort**: 5 min

### 3. `hash_zero_value` (tree.v:310) - DUPLICATE
**Status**: Duplicate of crypto.v:143
**Action**: Import from crypto.v instead
**Effort**: 2 min

### 4. `hash_zero_pair` (tree.v:314) - DUPLICATE
**Status**: Duplicate of crypto.v:145
**Action**: Import from crypto.v instead
**Effort**: 2 min

### 5. `hash_stem_respects_stem_eq` (crypto.v:117)
**Status**: Derivable from `stem_eq_true_wf` + function congruence
**Derivation**: If `stem_eq s1 s2 = true` and stems are well-formed, then `s1 = s2`, so `hash_stem s1 h = hash_stem s2 h` by reflexivity.
**Effort**: 10 min

### 6. `verkle_commit_deterministic` - Already a lemma
**Status**: Already proven (verkle.v:68-69)
**Action**: None needed

### 7. `batch_same_key_consistent` (tree.v:1133)
**Status**: Derivable from `hash_pair_collision_resistant` + Merkle structure
**Derivation**: Two valid inclusion proofs for same key compute same root. By CR, the leaf hashes must be equal, hence values equal.
**Effort**: 30 min

### 8. `tree_eq_implies_stems_eq` (verkle.v:286)
**Status**: Derivable from `tree_eq` definition (extensional equality)
**Derivation**: If `tree_eq t1 t2`, then for all keys, `get t1 k = get t2 k`. This means stems must contain same data.
**Effort**: 45 min (requires structural induction on stems)

---

## Category: PROVABLE (26 axioms)

These require significant proof work but are mathematically provable.

### High Priority (Security-Critical)

| Axiom | File | Effort | Proof Sketch |
|-------|------|--------|--------------|
| `inclusion_proof_soundness` | tree.v:1047 | 2h | Induction on witness length, apply `hash_pair_collision_resistant` at each step |
| `exclusion_proof_soundness` | tree.v:1055 | 2h | Similar to inclusion, but for zero paths |
| `multiproof_soundness` | tree.v:1232 | 3h | Decompose multiproof into individual paths, reduce to inclusion soundness |
| `verkle_verified_implies_tree_membership` | verkle.v:154 | 3h | Use `verkle_binding` to show value uniqueness |
| `witness_modification_changes_root` | security.v:424 | 2h | Use CR to show modified witness produces different root |
| `tree_binding_axiom` | security.v:588 | 1h | Corollary of CR axioms |

### Medium Priority (Correctness)

| Axiom | File | Effort | Proof Sketch |
|-------|------|--------|--------------|
| `insert_order_independent_subindex` | tree.v:894 | 1h | Use `sim_set_comm` on SubIndexMap level |
| `insert_order_independent` | tree_spec.v:173 | 1h | Similar, but for different-stem case |
| `get_insert_same` | tree_spec.v:182 | 30m | Unfold definitions, case split on stem match |
| `get_insert_other` | tree_spec.v:188 | 30m | Unfold definitions, show stems differ |
| `multiproof_completeness` | tree.v:1245 | 2h | Construct proof from tree structure |
| `verkle_witness_construction` | verkle.v:187 | 2h | Use `verkle_open_correct` for each position |
| `witness_generation_correct` | tree.v:910 | 2h | Show generate_multiproof produces valid paths |

### Lower Priority (Optimization/Streaming)

| Axiom | File | Effort | Proof Sketch |
|-------|------|--------|--------------|
| `stem_lt_trichotomy` | streaming.v:124 | 30m | Lexicographic ordering on byte lists |
| `stem_bit_at_spec` | streaming.v:311 | 30m | Arithmetic on bit extraction |
| `sort_entries_sorted` | streaming.v:379 | 1h | Standard sorting correctness |
| `sort_entries_permutation` | streaming.v:380 | 1h | Permutation lemmas |
| `subindex_map_to_array_aux_nth` | streaming.v:618 | 45m | Induction on array construction |
| `binary_tree_equals_fold` | streaming.v:698 | 1h | Binary tree hash equivalence |
| `hash_subindex_map_equiv` | streaming.v:717 | 1h | Map equivalence for hashing |
| `array_hash_equals_map_hash` | streaming.v:731 | 1h | Array/map hash correspondence |
| `tree_structure_hash_equiv` | streaming.v:790 | 2h | Full tree hash equivalence |

### Verkle Multi-proof (5 axioms)

| Axiom | File | Effort | Proof Sketch |
|-------|------|--------|--------------|
| `verkle_multi_open_correct` | verkle.v:326 | 1h | Batch open from singles |
| `verkle_multi_binding` | verkle.v:332 | 1h | Reduce to single binding |
| `verkle_multi_verify_decompose` | verkle.v:339 | 45m | Extract individual from batch |
| `verkle_aggregation_recovers_singles` | verkle.v:453 | 1h | Aggregation roundtrip |
| `verkle_aggregation_complete` | verkle.v:480 | 1h | Construction of aggregate |

---

## Category: REDUNDANT (15 axioms)

These are duplicates, trivially true, or can be eliminated.

### Duplicates (5)
| Axiom | Location | Duplicate Of | Action |
|-------|----------|--------------|--------|
| `hash_zero_value` | tree.v:310 | crypto.v:143 | Remove, import |
| `hash_zero_pair` | tree.v:314 | crypto.v:145 | Remove, import |
| `hash_zero` | tree_spec.v:69 | crypto.v:145 | Remove, import |
| `hash_single_zero` | tree_spec.v:70 | crypto.v:143 | Remove, import |
| `multiproof_soundness` | multiproof.v:260 | tree.v:1232 | Remove, import |

### Trivially Provable (4)
| Axiom | Location | Proof | Action |
|-------|----------|-------|--------|
| `verkle_natural_agg_axiom` | verkle.v:550 | Wrapper around `verkle_aggregation_complete` | Prove as lemma |
| `SHA256_length` | embedding_spec.v:181 | Property of SHA256 spec | Could prove from SHA256 def |
| `iter_no_duplicates` | iterator.v:226 | Structural property of iteration | Prove by induction |
| `insert_preserves_wf` | tree_spec.v:196 | Already proven in tree.v | Import |

### Complexity Specs (6) - Design Axioms
| Axiom | Location | Status |
|-------|----------|--------|
| `get_complexity` | complexity_spec.v:168 | Design spec, not provable in Rocq |
| `insert_complexity` | complexity_spec.v:173 | Design spec |
| `delete_complexity` | complexity_spec.v:177 | Design spec |
| `root_hash_full_complexity` | complexity_spec.v:199 | Design spec |
| `root_hash_incremental_complexity` | complexity_spec.v:204 | Design spec |
| `streaming_build_complexity` | complexity_spec.v:209 | Design spec |

*Note: Complexity axioms are intentionally design specifications and should remain as axioms.*

---

## Priority-Ordered Reduction Plan

### Phase 1: Quick Wins (1-2 hours) ✅ RECOMMENDED IMMEDIATE

1. **Remove duplicate `hash_zero_value` and `hash_zero_pair` from tree.v**
   - Import from crypto.v instead
   - Saves 2 axioms

2. **Convert `stem_eq_true` to use `stem_eq_true_wf`**
   - Add `wf_stem` preconditions where needed
   - Already have the proven lemma

3. **Convert `stem_eq_via_third` to use `stem_eq_trans`**
   - Same approach as above

4. **Remove duplicate axioms from tree_spec.v**
   - `hash_zero`, `hash_single_zero`, `insert_preserves_wf`

5. ✅ **COMPLETED: Convert `insert_order_independent_subindex` to lemma**
   - Proven using `sim_set_comm` helper lemma
   - Uses extensional tree equality definition

**Net reduction: 8 axioms → 59 remaining**

### Phase 2: Derivable Proofs (1 day)

5. **Prove `hash_stem_respects_stem_eq`**
   - Use stem equality + function congruence

6. **Prove `batch_same_key_consistent`**
   - Use Merkle CR properties

7. **Prove `tree_eq_implies_stems_eq`**
   - Extensional equality implies structural equality

**Net reduction: 3 axioms → 57 remaining**

### Phase 3: Security-Critical Proofs (1 week)

8. **Prove `inclusion_proof_soundness`**
   - Core security theorem
   - Induction on witness path

9. **Prove `exclusion_proof_soundness`**
   - Dual of inclusion

10. **Prove `multiproof_soundness`**
    - Reduces to individual proof soundness

11. **Prove `verkle_verified_implies_tree_membership`**
    - Uses PC binding

**Net reduction: 4 axioms → 53 remaining**

### Phase 4: Correctness Proofs (1-2 weeks)

12-18. Prove remaining PROVABLE axioms in order of dependency

**Final target: ~35 axioms (fundamental + complexity specs only)**

---

## Axioms That Must Remain

The following 24 axioms are truly fundamental and should not be reduced:

1. **Cryptographic (6)**: Collision resistance, binding properties
2. **Group Theory (6)**: Elliptic curve axioms for Verkle
3. **Execution (7)**: M monad semantics pending interpreter
4. **Complexity (6)**: Design specifications by nature

These represent the minimal trusted computing base for the verification.

---

## Appendix: Complete Axiom Inventory

### simulations/crypto.v (6 axioms)
- `hash_stem_respects_stem_eq` - DERIVABLE
- `hash_zero_value` - FUNDAMENTAL (design)
- `hash_zero_pair` - FUNDAMENTAL (design)
- `hash_value_collision_resistant` - FUNDAMENTAL (crypto)
- `hash_pair_collision_resistant` - FUNDAMENTAL (crypto)
- `hash_stem_collision_resistant` - FUNDAMENTAL (crypto)

### simulations/tree.v (9 axioms, 1 converted)
- `stem_eq_true` - DERIVABLE
- `hash_zero_value` - REDUNDANT (duplicate)
- `hash_zero_pair` - REDUNDANT (duplicate)
- `stem_eq_via_third` - DERIVABLE
- ~~`insert_order_independent_subindex`~~ - ✅ CONVERTED TO LEMMA
- `inclusion_proof_soundness` - PROVABLE
- `exclusion_proof_soundness` - PROVABLE
- `batch_same_key_consistent` - DERIVABLE
- `multiproof_soundness` - PROVABLE
- `multiproof_completeness` - PROVABLE

### simulations/verkle.v (13 axioms)
- `verkle_open_correct` - FUNDAMENTAL
- `verkle_binding` - FUNDAMENTAL
- `verkle_commit_zero` - PROVABLE
- `verkle_commit_injective` - FUNDAMENTAL
- `verkle_verified_implies_tree_membership` - PROVABLE
- `verkle_witness_construction` - PROVABLE
- `tree_eq_implies_stems_eq` - DERIVABLE
- `verkle_multi_open_correct` - PROVABLE
- `verkle_multi_binding` - PROVABLE
- `verkle_multi_verify_decompose` - PROVABLE
- `verkle_aggregation_recovers_singles` - PROVABLE
- `verkle_aggregation_complete` - PROVABLE
- `verkle_natural_agg_axiom` - REDUNDANT

### simulations/verkle_linking.v (14 axioms)
- `G_add_assoc` - FUNDAMENTAL
- `G_add_comm` - FUNDAMENTAL
- `G_add_identity` - FUNDAMENTAL
- `G_add_inverse` - FUNDAMENTAL
- `G_mul_distr` - PROVABLE (from group axioms)
- `G_mul_zero` - PROVABLE
- `G_mul_one` - PROVABLE
- `G_mul_assoc` - PROVABLE
- `pairing_bilinear` - FUNDAMENTAL
- `pairing_nondegen` - FUNDAMENTAL
- `pairing_bilinear_sym_axiom` - [AXIOM:HASHING] Symmetric bilinearity
- `verkle_binding_from_kzg_axiom` - [AXIOM:HASHING] Verkle-KZG binding link
- `multi_open_from_singles_axiom` - [AXIOM:HASHING] Multi-proof from singles
- `aggregation_preserves_binding_axiom` - [AXIOM:HASHING] Aggregation binding
- `IPA_binding_equivalent_to_KZG_axiom` - [AXIOM:HASHING] IPA-KZG equivalence

### simulations/streaming.v (9 axioms)
- `stem_lt_trichotomy` - PROVABLE
- `stem_bit_at_spec` - PROVABLE
- `sort_entries` (Parameter) - N/A
- `sort_entries_sorted` - PROVABLE
- `sort_entries_permutation` - PROVABLE
- `subindex_map_to_array_aux_nth` - PROVABLE
- `binary_tree_equals_fold` - PROVABLE
- `hash_subindex_map_equiv` - PROVABLE
- `array_hash_equals_map_hash` - PROVABLE
- `tree_structure_hash_equiv` - PROVABLE

### simulations/security.v (4 axioms)
- `witness_modification_changes_root` - PROVABLE
- `tree_binding_axiom` - PROVABLE
- `inclusion_completeness_construction` - PROVABLE
- `exclusion_completeness_construction` - PROVABLE
- `apply_insertions_permutation_invariant` - PROVABLE

### simulations/iterator.v (5 axioms)
- `keys_unique_axiom` - [AXIOM:ITERATOR] Key uniqueness
- `entries_match_get_axiom` - [AXIOM:ITERATOR] Entry-get correspondence
- `entry_count_sum_axiom` - [AXIOM:ITERATOR] Count equals sum of submaps
- `key_in_iff_get_some_axiom` - [AXIOM:ITERATOR] Key membership iff get returns Some
- `iter_no_duplicates` - PROVABLE

### specs/tree_spec.v (6 axioms)
- `hash_zero` - REDUNDANT
- `hash_single_zero` - REDUNDANT
- `insert_order_independent` - PROVABLE
- `get_insert_same` - PROVABLE
- `get_insert_other` - PROVABLE
- `insert_preserves_wf` - REDUNDANT

### simulations/complexity.v (6 axioms - NEW)
- `tree_proof_size_bound_axiom` - [AXIOM:COMPLEXITY] Tree proof bounded by MAX_DEPTH
- `proof_size_logarithmic_axiom` - [AXIOM:COMPLEXITY] Proof size O(depth)
- `stem_colocation_shared_tree_proof_axiom` - [AXIOM:STRUCTURAL] Same-stem shared tree proof
- `stem_colocation_reduces_proofs_axiom` - [AXIOM:STRUCTURAL] Same-stem proof reduction
- `multiproof_shared_stem_efficiency_axiom` - [AXIOM:COMPLEXITY] Multiproof deduplication
- `multiproof_more_efficient_axiom` - [AXIOM:COMPLEXITY] Multiproof efficiency

### specs/complexity_spec.v (6 axioms)
- All complexity axioms - FUNDAMENTAL (design specs)

### specs/embedding_spec.v (1 axiom)
- `SHA256_length` - PROVABLE

### linking/operations.v (10 axioms)
- `Run.run_pure` - FUNDAMENTAL
- `Run.run_bind` - FUNDAMENTAL
- `Run.run_panic` - FUNDAMENTAL
- `Run.run_eval_sound` - FUNDAMENTAL
- `get_executes` - FUNDAMENTAL
- `insert_executes` - FUNDAMENTAL
- `delete_executes` - FUNDAMENTAL
- `rust_verify_batch_inclusion_executes` - FUNDAMENTAL
- `rust_verify_shared_executes` - FUNDAMENTAL
- N/A (already lemmas or part of other modules)

### proofs/multiproof.v (6 axioms)
- `multiproof_soundness` - REDUNDANT (duplicate of tree.v)
- `multiproof_exclusion_soundness` - PROVABLE
- `multiproof_completeness` - REDUNDANT (duplicate)
- `witness_generation_correct` - PROVABLE
- `wf_multiproof_stems_cover` - PROVABLE
- `shared_deduplication_preserves_validity` - PROVABLE
- `witness_reflects_tree` - PROVABLE

### simulations/serialization.v (22 axioms) - NEW
Type-level roundtrip & canonical axioms (INTERFACE):
- `direction_roundtrip` - [AXIOM:ROUNDTRIP] Direction round-trip
- `direction_canonical` - [AXIOM:CANONICAL] Direction canonical encoding
- `direction_size` - [AXIOM:SIZE] Direction is 1 byte
- `treekey_roundtrip` - [AXIOM:ROUNDTRIP] TreeKey round-trip
- `treekey_canonical` - [AXIOM:CANONICAL] TreeKey canonical encoding
- `treekey_size` - [AXIOM:SIZE] TreeKey is 32 bytes
- `stem_roundtrip` - [AXIOM:ROUNDTRIP] Stem round-trip
- `stem_canonical` - [AXIOM:CANONICAL] Stem canonical encoding
- `stem_serialization_size` - [AXIOM:SIZE] Stem is 31 bytes
- `value_roundtrip` - [AXIOM:ROUNDTRIP] Value round-trip
- `value_canonical` - [AXIOM:CANONICAL] Value canonical encoding
- `value_serialization_size` - [AXIOM:SIZE] Value is 32 bytes
- `option_value_roundtrip` - [AXIOM:ROUNDTRIP] Optional value round-trip
- `option_value_canonical` - [AXIOM:CANONICAL] Optional value canonical
- `option_value_size` - [AXIOM:SIZE] Optional value 1 or 33 bytes
- `merkle_step_roundtrip` - [AXIOM:ROUNDTRIP] MerkleStep round-trip
- `merkle_step_canonical` - [AXIOM:CANONICAL] MerkleStep canonical
- `merkle_step_size` - [AXIOM:SIZE] MerkleStep is 33 bytes
- `merkle_witness_roundtrip` - [AXIOM:ROUNDTRIP] MerkleWitness round-trip
- `merkle_witness_canonical` - [AXIOM:CANONICAL] MerkleWitness canonical
- `merkle_witness_size` - [AXIOM:SIZE] MerkleWitness size formula
- `inclusion_proof_roundtrip` - [AXIOM:ROUNDTRIP] InclusionProof round-trip
- `inclusion_proof_canonical` - [AXIOM:CANONICAL] InclusionProof canonical
- `exclusion_proof_roundtrip` - [AXIOM:ROUNDTRIP] ExclusionProof round-trip
- `exclusion_proof_canonical` - [AXIOM:CANONICAL] ExclusionProof canonical
- `multiproof_roundtrip` - [AXIOM:ROUNDTRIP] MultiProof round-trip
- `multiproof_canonical` - [AXIOM:CANONICAL] MultiProof canonical
- `multiproof_serialization_size` - [AXIOM:SIZE] MultiProof size formula

Security axioms (DESIGN - interface specification for DoS prevention):
- `serialized_size_bounded` - [AXIOM:SECURITY] Serialized size bounded by multiproof_size + 16
- `deserialize_truncated_fails` - [AXIOM:SECURITY] Truncated input fails
- `invalid_tag_fails` - [AXIOM:SECURITY] Invalid option tags fail

Cross-type axioms (INTERFACE):
- `serialize_deterministic` - [AXIOM:DETERMINISM] Same value produces same bytes
- `inclusion_exclusion_disjoint` - [AXIOM:DISJOINT] Inclusion/exclusion have disjoint formats

**Categorization:**
- INTERFACE (28): Round-trip, canonical, size, determinism, disjoint axioms
  These specify the serialization interface contract with Rust implementation
- DESIGN (3): Security axioms (size bounded, truncated fails, invalid tag fails)
  These are design requirements that implementations must satisfy

**Priority:** Medium - These are interface axioms that would require proving
properties about the serialized byte format. Most can remain as axioms since
they represent the external serialization contract.

### linking/interpreter.v (18 axioms) - NEW
Encoding/Decoding axioms (INTERFACE):
- `decode_stem_correct` - [AXIOM:ENCODING] Stem encoding invertible
- `decode_stem_map_correct` - [AXIOM:ENCODING] StemMap encoding invertible
- `decode_subindex_map_correct` - [AXIOM:ENCODING] SubIndexMap encoding invertible

HashMap linking axioms (FUNDAMENTAL - awaiting full interpreter):
- `hashmap_get_refines` - [AXIOM:HASHMAP] HashMap::get matches simulation
- `hashmap_entry_or_insert_refines` - [AXIOM:HASHMAP] Entry pattern matches simulation
- `subindexmap_get_refines` - [AXIOM:SUBINDEXMAP] SubIndexMap::get matches simulation
- `hashmap_get_steps` - [AXIOM:HASHMAP] HashMap.get stepping
- `subindexmap_get_steps` - [AXIOM:SUBINDEXMAP] SubIndexMap.get stepping

Termination axioms (PROVABLE - after full interpreter):
- `get_terminates` - [AXIOM:TERMINATION] Get terminates with sufficient fuel
- `insert_terminates` - [AXIOM:TERMINATION] Insert terminates
- `delete_terminates` - [AXIOM:TERMINATION] Delete terminates

Correctness axioms (PROVABLE - after full interpreter):
- `get_correct` - [AXIOM:CORRECTNESS] Get returns correct value
- `insert_correct` - [AXIOM:CORRECTNESS] Insert preserves refinement
- `delete_correct` - [AXIOM:CORRECTNESS] Delete preserves refinement

Panic freedom axioms (PROVABLE - after correctness proofs):
- `get_no_panic` - [AXIOM:PANIC-FREE] Get never panics on wf input
- `insert_no_panic` - [AXIOM:PANIC-FREE] Insert never panics on wf input

Fuel properties (PROVABLE):
- `fuel_monotonic` - [AXIOM:FUEL] More fuel doesn't change success
- `let_compose` - [AXIOM:FUEL] Sequential composition fuel bounds

**Categorization:**
- INTERFACE (3): Encoding axioms - specify φ encoding contract
- FUNDAMENTAL (5): HashMap linking - require full step semantics implementation
- PROVABLE (10): Termination, correctness, panic-freedom, fuel properties
  These become provable once the interpreter step semantics are complete

**Priority:** High - These axioms block the full linking proof roadmap.
The interpreter work (Issue #24) targets converting these to theorems.
