# Verkle Tree Security Model

This document describes the security model, cryptographic assumptions, and verification status of the Verkle tree formalization in `formal/simulations/verkle.v`.

## Overview

Verkle trees replace hash-based Merkle proofs with polynomial commitment-based proofs, offering O(1) proof sizes instead of O(log n). The security of Verkle trees reduces to the security of the underlying polynomial commitment scheme (KZG or IPA).

## Security Model

### Threat Model

The formal verification assumes an adversary who:
- Has access to the tree root commitment
- Can observe valid proofs
- Attempts to forge proofs for values not in the tree
- Cannot solve the discrete logarithm problem in the commitment group

### Security Properties Verified

| Property | Status | Axiom/Lemma |
|----------|--------|-------------|
| Inclusion Soundness | Axiom | `verkle_verified_implies_tree_membership` |
| Exclusion Soundness | Axiom | `verkle_exclusion_soundness_axiom` |
| Inclusion Completeness | Axiom | `verkle_witness_construction` |
| Exclusion Completeness | Axiom | `verkle_exclusion_completeness_axiom` |
| Binding (PC level) | Axiom | `verkle_binding` |
| Proof Aggregation | Axiom | `verkle_aggregation_recovers_singles` |
| Mutual Exclusivity | Proven | `verkle_exclusion_inclusion_exclusive` |

## Cryptographic Assumptions

### KZG Polynomial Commitments

The KZG (Kate-Zaverucha-Goldberg) scheme relies on:

1. **q-SDH (q-Strong Diffie-Hellman) Assumption**
   - Given `(g, g^s, g^{s^2}, ..., g^{s^q})` for random `s`
   - Hard to compute `(c, g^{1/(s+c)})` for any `c`
   - Security parameter: ~128 bits with BLS12-381

2. **Trusted Setup**
   - Requires structured reference string (SRS) from trusted ceremony
   - SRS: `(g, g^s, g^{s^2}, ..., g^{s^d})` for degree-d polynomials
   - Ethereum uses KZG ceremony with 140,000+ participants

3. **Pairing Assumption**
   - Bilinear pairing `e: G1 × G2 → GT` is efficiently computable
   - BLS12-381 provides ~128-bit security

**Literature Reference:**
- Kate, Zaverucha, Goldberg. "Constant-Size Commitments to Polynomials and Their Applications" (ASIACRYPT 2010)

### IPA (Inner Product Argument) Polynomial Commitments

Alternative to KZG without trusted setup:

1. **Discrete Log Assumption**
   - Given `g, h = g^x`, hard to compute `x`
   - No structured reference string needed

2. **Pedersen Commitment Hiding/Binding**
   - Computationally binding under DL
   - Perfectly hiding (information-theoretic)

3. **Trade-offs vs KZG**
   - No trusted setup required
   - Proof verification is O(n) instead of O(1)
   - Proofs are larger: O(log n) group elements

**Literature Reference:**
- Bünz et al. "Bulletproofs: Short Proofs for Confidential Transactions and More" (S&P 2018)

## Axiom Justification

### Core Polynomial Commitment Axioms

#### `verkle_open_correct`
```coq
Axiom verkle_open_correct : forall values idx,
  (0 <= idx < Z.of_nat (length values))%Z ->
  verkle_verify (verkle_commit values) idx v (verkle_open ...) = true.
```
**Justification:** Standard correctness property of polynomial commitments. Any honestly-generated opening proof verifies. This is unconditionally true for both KZG and IPA.

#### `verkle_binding`
```coq
Axiom verkle_binding : forall c idx v1 v2 proof1 proof2,
  verkle_verify c idx v1 proof1 = true ->
  verkle_verify c idx v2 proof2 = true ->
  v1 = v2.
```
**Justification:** The binding property is the core security guarantee. Breaking it requires:
- KZG: Solving q-SDH (finding polynomial with same commitment but different evaluation)
- IPA: Breaking discrete log (finding different Pedersen commitment opening)

**Security Reduction:** Given an adversary that breaks binding, we can construct a q-SDH solver (KZG) or DL solver (IPA).

#### `verkle_commit_injective`
```coq
Axiom verkle_commit_injective : forall v1 v2,
  verkle_commit v1 = verkle_commit v2 ->
  length v1 = length v2 ->
  v1 = v2.
```
**Justification:** Follows from binding. If two different polynomials had the same commitment, opening at any differing coefficient would break binding.

### Tree-Level Axioms

#### `verkle_verified_implies_tree_membership`
**Justification:** Composes two binding properties:
1. Stem commitment binds subindex → value
2. Root commitment binds stem index → stem commitment

An adversary forging a proof for wrong value must break one of these bindings.

#### `verkle_exclusion_soundness_axiom`
**Justification:** Same binding reduction. If the tree contained a non-zero value at key k, opening to zero32 at that position would break binding.

#### `verkle_exclusion_completeness_axiom`
**Justification:** Constructive property. The tree commits to zero32 at absent positions, so we can generate valid zero-openings.

## What Would Be Needed for Full Verification

### Currently Axiomatized (Requires External Proofs)

1. **Polynomial Commitment Binding**
   - Formal proof that KZG binding holds under q-SDH
   - Would require: formalization of elliptic curve groups, pairings, polynomial arithmetic
   - Estimated effort: Major research project (1-2 years)
   - Existing work: Fiat-Crypto provides some EC primitives

2. **Cryptographic Group Operations**
   - BLS12-381 curve arithmetic
   - Pairing computation
   - Point serialization/deserialization
   - Reference: Fiat-Crypto, Hacspec

3. **Random Oracle Model**
   - Fiat-Shamir transformation for non-interactive proofs
   - Domain separation for hash functions

### Path to Reduced Trust

1. **Link to Verified Crypto Libraries**
   ```
   verkle.v (tree logic)
        ↓
   kzg.v (PC interface)
        ↓
   fiat_crypto.v (EC operations)
        ↓
   machine integers (VST/CompCert)
   ```

2. **Verification Targets by Priority**
   - High: Tree structure ↔ commitment correspondence
   - Medium: Aggregation preserves individual validity
   - Lower: Cryptographic primitive correctness (defer to specialized libraries)

3. **Recommended Approach**
   - Accept crypto axioms as interface to verified crypto library
   - Focus verification on tree logic and proof composition
   - Audit crypto axioms against well-established literature

## Proof Size Analysis

### Formalized Bounds

```coq
Definition COMMITMENT_SIZE : nat := 48.   (* BLS12-381 G1 compressed *)
Definition FIELD_ELEMENT_SIZE : nat := 32. (* 256-bit scalar *)
Definition PROOF_ELEMENT_SIZE : nat := 48. (* KZG proof point *)
```

| Proof Type | Size Formula | Typical Size |
|------------|--------------|--------------|
| Single Verkle | 2×48 + 2×48 + 32 = 224 bytes | ~224 B |
| Aggregated (n keys) | 96 + 96 + n×32 bytes | ~192 + 32n B |
| Merkle (depth d) | d × 32 bytes | 32d B |

### Crossover Point

Verkle proofs are smaller than Merkle proofs when:
```
224 < 32 × depth
depth > 7
```

For trees of depth ≥8, Verkle provides space savings. Ethereum state trees typically have depth 20-40.

## Security Considerations

### Known Limitations

1. **Zero-Value Ambiguity**
   - `sim_tree_get t k = None` and `sim_tree_get t k = Some zero32` are indistinguishable
   - This is by design (sparse tree optimization) but requires care in applications

2. **Commitment Uniqueness**
   - Tree comparison uses commitment equality, not value equality
   - Different tree construction orders may produce different intermediate commitments
   - Root commitment is unique for a given set of key-value pairs

3. **Multi-Proof Malleability**
   - Aggregated proofs may have multiple valid representations
   - Binding still holds: cannot forge values, only restructure proof

### Audit Recommendations

1. Review axiom statements against published literature
2. Ensure axiom dependencies don't create circular reasoning
3. Validate that proven theorems actually use axioms correctly
4. Cross-reference with Ethereum Verkle tree specifications (EIP-6800)

## References

1. Kate, Zaverucha, Goldberg. "Constant-Size Commitments to Polynomials and Their Applications" ASIACRYPT 2010
2. Bünz et al. "Bulletproofs: Short Proofs for Confidential Transactions" S&P 2018  
3. Khovratovich, Buterin. "Verkle Tree Structure" EIP-6800
4. Drake. "Verkle Trees for Statelessness" Ethereum Research
5. Gabizon, Williamson, Ciobotaru. "PLONK: Permutations over Lagrange-bases" 2019
6. Fiat-Crypto: https://github.com/mit-plv/fiat-crypto

## Version History

| Date | Change |
|------|--------|
| 2024-12 | Initial security documentation |
| 2024-12 | Added exclusion proof soundness/completeness |
| 2024-12 | Formalized proof size bounds |
