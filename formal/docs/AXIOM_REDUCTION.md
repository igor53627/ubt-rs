# UBT Axiom Reduction Analysis

**Issue:** #14 - Reduce axiom count  
**Date:** December 2024  
**Current Count:** 64 axioms (per axiom_audit.md)  
**Target Count:** ~55 axioms after reduction

---

## Executive Summary

Analysis of the 64 axioms reveals:
- **9 axioms are clearly derivable** and can be converted to lemmas
- **4 axioms might be derivable** with additional work
- **51 axioms must remain** (crypto primitives, design choices, implementation gaps)

### Already Converted (in current codebase)

The following were listed as axioms in axiom_audit.md but are **already lemmas**:
1. `hash_deterministic_value` (crypto.v) - proven via rewrite/reflexivity
2. `hash_deterministic_pair` (crypto.v) - proven via rewrite/reflexivity
3. `hash_deterministic_stem` (crypto.v) - proven using `hash_stem_respects_stem_eq`
4. `hash_value_second_preimage` (crypto.v) - proven from collision resistance
5. `hash_value_nonzero` (crypto.v) - proven from collision resistance + zero hash
6. `verkle_hiding` (verkle.v) - trivially provable (conclusion is True)
7. `verkle_commit_deterministic` (verkle.v) - proven via rewrite/reflexivity
8. `nth_error_key_unique` (verkle.v) - proven from NoDup_nth_error
9. `hash_deterministic` (tree_spec.v) - proven via reflexivity
10. `hash_collision_resistant` (tree_spec.v) - trivially provable (`\/ True`)
11. `hash_injective` (tree_spec.v) - trivially provable (conclusion is `True`)

These 11 items are already lemmas, so the **actual current axiom count is ~53**, not 64.

---

## Axioms That Can Be Converted to Lemmas

### 1. `insert_order_independent_subindex` (tree.v:720-725)

**Current:** Axiom stating same-stem, different-subindex inserts commute.

**Derivation:** Can be proven using `sim_set_comm` lemma which is already in the file.

```coq
(* Proof sketch *)
Theorem insert_order_independent_subindex : forall t k1 v1 k2 v2,
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  tk_subindex k1 <> tk_subindex k2 ->
  tree_eq 
    (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
    (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  intros t k1 v1 k2 v2 Hstem Hidx.
  unfold tree_eq. intros k.
  (* Use sim_set_comm and stem equality properties *)
  (* Case analysis on whether k matches k1/k2 stems *)
  ...
Qed.
```

**Priority:** HIGH - Pure algebraic property, no crypto assumptions needed.

### 2. `stem_eq_true` (tree.v:152)

**Current:** Axiom stating `stem_eq s1 s2 = true -> s1 = s2`.

**Derivation:** Already have `stem_eq_true_wf` which proves this for well-formed stems (31 bytes). Can either:
- Add well-formedness precondition to all uses
- Or prove from a well-formedness invariant axiom

**Priority:** MEDIUM - Requires threading well-formedness through proofs.

### 3. `stem_eq_via_third` (tree.v:395-398)

**Current:** Axiom for stem equality transitivity.

**Derivation:** Already have `stem_eq_trans` which proves this with length preconditions. Same resolution as `stem_eq_true`.

**Priority:** MEDIUM - Same treatment as stem_eq_true.

---

## Axioms That Might Be Derivable (Needs Investigation)

### 1. `tree_eq_implies_stems_eq` (verkle.v:286-289)

**Current:** `tree_eq t1 t2 -> st_stems t1 = st_stems t2`

**Issue:** This assumes canonical representation. May need to be kept as a design axiom or proven with additional representation invariants.

**Investigation needed:** Can we prove that `tree_eq` (pointwise equality of `sim_tree_get`) implies structural equality?

### 2. `insert_order_independent` (tree_spec.v:173-177)

**Current:** Order independence for `tree_insert` parameter.

**Issue:** `tree_insert` is a Parameter, not defined. This can't be proven without implementation.

**Resolution:** Keep as axiom until tree_insert is defined.

### 3. Spec axioms: `get_insert_same`, `get_insert_other`, `insert_preserves_wf` (tree_spec.v)

**Current:** Axioms for tree_insert behavior.

**Issue:** These use the parametric `tree_insert`, not `sim_tree_insert`. The simulation versions are theorems.

**Resolution:** Keep as specification axioms. They're the contract that any implementation must satisfy.

### 4. `batch_same_key_consistent` (tree.v:960-964)

**Current:** Two valid proofs for same key must have same value.

**Derivation:** Should follow from `inclusion_proof_soundness` - if both proofs verify against root, both values are in tree at same key, and tree is a function.

```coq
(* Proof sketch *)
Theorem batch_same_key_consistent' :
  forall (root : Bytes32) (p1 p2 : InclusionProof),
    ip_key p1 = ip_key p2 ->
    verify_inclusion_proof p1 root ->
    verify_inclusion_proof p2 root ->
    ip_value p1 = ip_value p2.
Proof.
  intros root p1 p2 Hkey Hv1 Hv2.
  (* Both proofs verify, so by soundness, both values are at the key *)
  (* But this requires knowing which tree the root came from *)
  (* The issue is we only have the root, not the tree *)
  (* This requires collision resistance argument *)
Admitted.
```

**Priority:** LOW - Requires careful collision resistance argument.

---

## Axioms That Must Remain

### Category 1: Cryptographic Primitives (Cannot be proven in type theory)

| Axiom | File | Reason |
|-------|------|--------|
| `hash_value` | crypto.v | Parameter - abstract hash function |
| `hash_pair` | crypto.v | Parameter - abstract hash function |
| `hash_stem` | crypto.v | Parameter - abstract hash function |
| `hash_zero_value` | crypto.v | Design choice (EIP-7864) |
| `hash_zero_pair` | crypto.v | Design choice (EIP-7864) |
| `hash_stem_respects_stem_eq` | crypto.v | Hash treats equal stems identically |
| `hash_value_collision_resistant` | crypto.v | Standard crypto assumption |
| `hash_pair_collision_resistant` | crypto.v | Standard crypto assumption |
| `hash_stem_collision_resistant` | crypto.v | Standard crypto assumption |

### Category 2: Verkle Polynomial Commitment (Cannot be proven without crypto)

| Axiom | File | Reason |
|-------|------|--------|
| `VerkleCommitment` | verkle.v | Abstract type parameter |
| `VerkleProof` | verkle.v | Abstract type parameter |
| `verkle_commit` et al. | verkle.v | Abstract operations |
| `verkle_open_correct` | verkle.v | Standard PC property |
| `verkle_binding` | verkle.v | Critical security property |
| `verkle_commit_zero` | verkle.v | Design choice |
| `verkle_commit_injective` | verkle.v | Standard PC property |
| `verkle_multi_*` | verkle.v | Batch proof properties |
| `verkle_verified_implies_tree_membership` | verkle.v | Soundness |
| `verkle_witness_construction` | verkle.v | Completeness |
| `verkle_aggregation_*` | verkle.v | Aggregation properties |
| `verkle_natural_agg_axiom` | verkle.v | Batch-open property |

### Category 3: Linking Layer (Implementation gap)

| Axiom | File | Reason |
|-------|------|--------|
| `Run.run_*` | operations.v | M monad semantics |
| `*_executes` axioms | operations.v | Rust↔simulation linking |
| `*_no_panic` axioms | operations.v | Panic freedom |
| `rust_verify_*` axioms | operations.v | Batch verification |

### Category 4: Security Proofs (Structural security)

| Axiom | File | Reason |
|-------|------|--------|
| `witness_modification_changes_root` | security.v | Non-malleability |
| `inclusion_proof_soundness` | tree.v | Merkle soundness |
| `exclusion_proof_soundness` | tree.v | Merkle soundness |

---

## Recommended Actions

### Immediate (Can do now)

1. **Convert `insert_order_independent_subindex` to lemma**
   - File: `simulations/tree.v`
   - Use existing `sim_set_comm` helper
   - Estimated complexity: Medium

### Short-term

2. **Add well-formedness invariant for stems**
   - All stems in tree have 31 bytes
   - Then convert `stem_eq_true` and `stem_eq_via_third` to lemmas with `wf_stem` precondition

3. **Update axiom_audit.md**
   - Correct the count (many "axioms" are already lemmas)
   - Current actual axiom count: ~53

### Medium-term

4. **Investigate `batch_same_key_consistent`**
   - May be provable from inclusion_proof_soundness + tree binding

5. **Define `tree_insert` in tree_spec.v**
   - Currently a Parameter, making axioms necessary
   - Define as `sim_tree_insert` or equivalent

---

## Updated Axiom Count After Reduction

| Category | Before | After | Notes |
|----------|--------|-------|-------|
| Hash Crypto | 9 | 9 | All essential |
| Verkle Crypto | 18 | 18 | All essential |
| Design (zero hash) | 4 | 4 | EIP-7864 spec |
| Structural (stem_eq) | 2 | 0-2 | Depends on wf approach |
| Tree spec axioms | 4 | 4 | Until tree_insert defined |
| Linking axioms | 14 | 14 | Until M monad interpreter |
| Security axioms | 3 | 2-3 | batch_same_key may be provable |
| **Total** | **54** | **~51** | Reduction of ~3 |

Note: The axiom_audit.md listed 64-67 axioms, but 11 are already lemmas in the actual code, so true baseline is ~53-54.

---

## Files Modified

After implementing reductions:
- `formal/simulations/tree.v` - Convert `insert_order_independent_subindex`
- `formal/docs/axiom_audit.md` - Update counts and status

---

*Last updated: December 2024*
