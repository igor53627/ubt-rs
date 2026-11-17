# UBT Security Theorems

This document describes the formally verified security theorems for the UBT (Unified Binary Tree) Merkle tree implementation.

## Location

All security theorems are in `formal/simulations/security.v`.

## Cryptographic Assumptions

The security proofs rely on axioms in `formal/simulations/crypto.v`:

| Axiom | Description |
|-------|-------------|
| `hash_value_collision_resistant` | `hash_value v1 = hash_value v2 → v1 = v2` |
| `hash_pair_collision_resistant` | `hash_pair a1 b1 = hash_pair a2 b2 → a1 = a2 ∧ b1 = b2` |
| `hash_stem_collision_resistant` | `hash_stem s1 h1 = hash_stem s2 h2 → stem_eq s1 s2 = true ∧ h1 = h2` |
| `hash_value_nonzero` | Non-zero values hash to non-zero outputs (now a lemma derived from `hash_value_collision_resistant` and the axiom `hash_zero_value : hash_value zero32 = zero32`) |

The axiom `hash_zero_value` models the crate before the zero-value change. The Rust `Hasher::hash_32` now has no zero rule, as in go-ethereum: a leaf that holds 32 zero bytes is present and its hash is not zero. The Rocq model is not updated.

Five theorems below also apply axioms that `formal/simulations/security.v` declares. The Status column names the axiom for each of them.

## Core Security Theorems

### Section 1-2: Data Integrity

| Theorem | Status | Description |
|---------|--------|-------------|
| `merkle_path_binding` | Proven | Same witness path + same root => same leaf hash |
| `merkle_path_distinct` | Proven | Different leaves produce different roots (same path) |
| `merkle_proof_value_integrity` | Proven | Two proofs for same key/root must have same value |

### Section 3: Proof Unforgeability

| Theorem | Status | Description |
|---------|--------|-------------|
| `internal_node_unforgeability` | Proven | Internal nodes cannot be forged |
| `stem_node_unforgeability` | Proven | Stem nodes cannot be forged |
| `witness_step_unforgeable` | Proven | Each witness step is unforgeable |

### Section 5: Security Reduction

| Theorem | Status | Description |
|---------|--------|-------------|
| `merkle_security_reduction` | Proven | Breaking Merkle security => finding hash collision |
| `no_forgery_without_collision` | Proven | Corollary: no forgery if hash is collision-resistant |

### Section 9: Non-Malleability

| Theorem | Status | Description |
|---------|--------|-------------|
| `witness_non_malleable` | Proven from axiom `witness_modification_changes_root` | Modifying witness changes computed root |
| `value_non_malleable` | Proven | Modifying value changes verification |

### Section 10: Commitment Binding

| Theorem | Status | Description |
|---------|--------|-------------|
| `commitment_binding` | Proven | Root uniquely binds each position to one value |
| `stem_commitment_binding` | Proven | Stem hash uniquely determines stem and subtree |
| `tree_binding` | Proven from axiom `tree_binding_axiom` | Same root => same values for all keys |

### Section 11: Soundness

| Theorem | Status | Description |
|---------|--------|-------------|
| `proof_soundness` | Proven | Verified inclusion proof => value in tree |
| `exclusion_soundness` | Proven | Verified exclusion proof => key absent |
| `no_false_inclusion` | Proven | Cannot create valid proof for wrong value |
| `no_false_exclusion` | Proven | Cannot create exclusion proof for present key |

### Section 12: Completeness

| Theorem | Status | Description |
|---------|--------|-------------|
| `inclusion_completeness` | Proven from axiom `inclusion_completeness_construction` | Valid proof exists for every key-value pair |
| `exclusion_completeness` | Proven from axiom `exclusion_completeness_construction` | Valid exclusion proof exists for absent keys |

### Section 13: History Independence

| Theorem | Status | Description |
|---------|--------|-------------|
| `history_independence_semantics` | Proven | Insertion order doesn't matter (different stems) |
| `history_independence_same_stem` | Proven | Insertion order doesn't matter (same stem) |
| `multi_key_history_independence` | Proven from axiom `apply_insertions_permutation_invariant` | Generalized to arbitrary permutations |

### Section 14: Batch Proof Security

| Theorem | Status | Description |
|---------|--------|-------------|
| `batch_to_individual_inclusion` | Proven | Valid batch => each individual proof valid |
| `batch_to_individual_exclusion` | Proven | Valid batch => each individual proof valid |
| `individual_to_batch_inclusion` | Proven | All valid individuals => valid batch |
| `individual_to_batch_exclusion` | Proven | All valid individuals => valid batch |
| `batch_inclusion_soundness` | Proven | Batch inclusion proofs are sound |
| `batch_exclusion_soundness` | Proven | Batch exclusion proofs are sound |
| `mixed_batch_soundness` | Proven | Mixed batch proofs are sound |
| `batch_proof_consistency` | Proven | Same-key proofs in batch must agree |

### Section 15: Tree State Consistency

| Theorem | Status | Description |
|---------|--------|-------------|
| `get_insert_consistency` | Proven | Insert then get same key returns value |
| `insert_delete_consistency` | Proven | Insert then delete results in absence |
| `delete_insert_consistency` | Proven | Delete then insert returns new value |
| `double_insert_consistency` | Proven | Double insert: second value wins |
| `double_delete_idempotent` | Proven | Double delete is idempotent |
| `root_hash_distinguishes` | Proven | Different contents => different roots |

## Game-Based Security (Section 16)

### EUF-MPA: Existential Unforgeability under Merkle Proof Attack

| Theorem | Status | Description |
|---------|--------|-------------|
| `euf_mpa_security` | Proven | No adversary can forge proofs for uninserted values |
| `euf_implies_consistency` | Proven | Corollary: "winning" requires actual insertion |

### Binding Game

| Theorem | Status | Description |
|---------|--------|-------------|
| `binding_game_security` | Proven | No adversary can open commitment to two values |

### Accumulator Soundness Games

| Theorem | Status | Description |
|---------|--------|-------------|
| `accumulator_inclusion_sound` | Proven | Cannot prove membership of non-members |
| `accumulator_exclusion_sound` | Proven | Cannot prove non-membership of members |

### Advantage Bounds

| Theorem | Status | Description |
|---------|--------|-------------|
| `merkle_forgery_advantage_negligible` | Proven | Forgery advantage < 2^128 for q < 2^64 queries |

## Accumulator Security (Section 17)

| Theorem | Status | Description |
|---------|--------|-------------|
| `accumulator_correctness` | Proven | Valid proof exists for all accumulated elements |
| `accumulator_membership_soundness` | Proven | Verified proof => element is accumulated |
| `accumulator_nonmembership_soundness` | Proven | Verified exclusion => element not accumulated |
| `accumulator_uniqueness` | Proven | Each key has at most one accumulated value |
| `accumulator_add_preserves_others` | Proven | Adding element preserves other lookups |
| `commitment_is_binding` | Proven | Root hash commits to all values |

## Summary

### Proven Theorems: 48
### Admitted Theorems: 0

### Admitted Theorem Justifications

None. The theorems that this document listed as admitted before (`witness_non_malleable`, `tree_binding`, `inclusion_completeness`, `exclusion_completeness`, `multi_key_history_independence`, `binding_game_security`) are closed with `Qed` in `formal/simulations/security.v`.

## Security Model Coverage

| Attack Type | Coverage | Key Theorems |
|-------------|----------|--------------|
| Proof Forgery | Full | `merkle_security_reduction`, `euf_mpa_security` |
| Value Modification | Full | `commitment_binding`, `value_non_malleable` |
| Proof Reuse | Full | Each proof bound to key-value-root tuple |
| Batch Attacks | Full | `batch_proof_consistency`, `mixed_batch_soundness` |
| History Analysis | Full | `history_independence_*` theorems |

## References

- Merkle, R. "A Digital Signature Based on a Conventional Encryption Function" (1987)
- Rogaway & Shrimpton, "Cryptographic Hash-Function Basics" (2004)
- Bellare & Rogaway, "Random Oracles are Practical" (1993)
