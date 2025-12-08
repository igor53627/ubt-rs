# Verification Scope

**Status:** **VERIFICATION COMPLETE** (December 2024)

This document defines the boundaries of what is formally verified in the UBT implementation, what relies on external assumptions, and what is out of scope.

| Metric | Value |
|--------|-------|
| Total Axioms | 67 |
| Parameters | 26 |
| Admitted Proofs | **0** (all closed) |
| QuickChick Tests | 5 properties, 50,000 total tests |
| OCaml Extraction | 10/10 tests passing |
| FFI Bridge | Created |

---

## What Is Formally Verified

The following properties are proven in Rocq with machine-checked proofs. These theorems compose to provide end-to-end correctness guarantees for the core UBT operations.

### Core Tree Operations

| Theorem | Location | Statement |
|---------|----------|-----------|
| `get_empty` | [simulations/tree.v](../simulations/tree.v) | `sim_tree_get empty_tree k = None` |
| `get_insert_same` | [simulations/tree.v](../simulations/tree.v) | `sim_tree_get (sim_tree_insert t k v) k = Some v` (when v ≠ 0) |
| `get_insert_other_stem` | [simulations/tree.v](../simulations/tree.v) | Insert at k₁ doesn't affect get at k₂ when stems differ |
| `get_insert_other_subindex` | [simulations/tree.v](../simulations/tree.v) | Insert at k₁ doesn't affect get at k₂ when same stem, different subindex |
| `get_delete` | [simulations/tree.v](../simulations/tree.v) | `sim_tree_get (sim_tree_delete t k) k = None` |
| `insert_preserves_wf` | [simulations/tree.v](../simulations/tree.v) | Well-formedness is preserved by insert |

### Hash Properties

| Theorem | Location | Statement |
|---------|----------|-----------|
| `empty_tree_zero_hash` | [proofs/correctness.v](../proofs/correctness.v) | `sim_node_hash SimEmpty = zero32` |
| `hash_deterministic` | [proofs/correctness.v](../proofs/correctness.v) | Same tree → same hash (functional purity) |
| `sim_root_hash_empty` | [simulations/tree.v](../simulations/tree.v) | Empty tree root hash is zero |

### Merkle Proof Soundness

| Theorem | Location | Statement |
|---------|----------|-----------|
| `inclusion_proof_soundness` | [simulations/tree.v](../simulations/tree.v) | Valid proof ⟹ key-value exists in tree |
| `witness_collision_resistant_same_path` | [simulations/tree.v](../simulations/tree.v) | Same witness path → same value |
| `inclusion_proof_binding_strong` | [simulations/tree.v](../simulations/tree.v) | Same witnesses ⟹ same value |

### Merkle Proof Completeness

| Theorem | Location | Statement |
|---------|----------|-----------|
| `inclusion_proof_completeness` | [simulations/tree.v](../simulations/tree.v) | Value exists ⟹ inclusion proof exists |
| `exclusion_completeness` | [simulations/tree.v](../simulations/tree.v) | Key absent ⟹ exclusion proof exists |

### State Diff Correctness

| Theorem | Location | Statement |
|---------|----------|-----------|
| `compute_diff_valid` | [simulations/tree.v](../simulations/tree.v) | Computed diff correctly describes changes |
| `diff_proof_sound` | [simulations/tree.v](../simulations/tree.v) | Valid diff proof ⟹ trees differ as claimed |
| `diff_complete` | [simulations/tree.v](../simulations/tree.v) | For any two trees, a valid diff exists |
| `diff_minimal` | [simulations/tree.v](../simulations/tree.v) | Computed diff contains only changed keys |
| `diff_inverse_valid` | [simulations/tree.v](../simulations/tree.v) | Inverted diff is valid in reverse direction |

### Batch Verification Equivalence

| Theorem | Location | Statement |
|---------|----------|-----------|
| `batch_creates_diff` | [simulations/tree.v](../simulations/tree.v) | Batch operation creates corresponding diff |
| `diff_as_operations` | [simulations/tree.v](../simulations/tree.v) | Diff can be expressed as sequence of operations |

### Co-location (EIP-7864)

| Theorem | Location | Statement |
|---------|----------|-----------|
| `keys_share_stem_node` | [proofs/correctness.v](../proofs/correctness.v) | Keys with same stem share StemNode |
| `account_data_same_stem` | [specs/embedding_spec.v](../specs/embedding_spec.v) | Basic data and code hash share stem |
| `header_storage_same_stem` | [specs/embedding_spec.v](../specs/embedding_spec.v) | First 64 storage slots share account stem |
| `code_chunks_same_group_stem` | [specs/embedding_spec.v](../specs/embedding_spec.v) | Nearby code chunks share stem |
| `account_colocation_holds` | [specs/embedding_spec.v](../specs/embedding_spec.v) | Full account co-location theorem |

### Order Independence

| Theorem | Location | Status |
|---------|----------|--------|
| `insert_order_independent_stems` | [simulations/tree.v](../simulations/tree.v) | Fully proven |
| `insert_order_independent_subindex` | [simulations/tree.v](../simulations/tree.v) | Fully proven |

### Security Properties (Game-Based)

| Theorem | Location | Statement |
|---------|----------|-----------|
| `merkle_path_binding` | [simulations/security.v](../simulations/security.v) | Same path + root ⟹ same leaf |
| `euf_mpa_security` | [simulations/security.v](../simulations/security.v) | Existential unforgeability under Merkle proof attack |
| `binding_game_security` | [simulations/security.v](../simulations/security.v) | No adversary wins binding game |
| `accumulator_inclusion_sound` | [simulations/security.v](../simulations/security.v) | Cannot prove membership of non-members |
| `accumulator_exclusion_sound` | [simulations/security.v](../simulations/security.v) | Cannot prove non-membership of members |
| `merkle_forgery_advantage_negligible` | [simulations/security.v](../simulations/security.v) | Forgery advantage bounded by 2^-128 |

---

## What Relies on Cryptographic Assumptions

These axioms encode standard cryptographic hardness assumptions. They are **intentionally** axioms—proving them would contradict their security properties.

### Collision Resistance

| Axiom | Location | Dependents |
|-------|----------|------------|
| `hash_value_collision_resistant` | [simulations/tree.v](../simulations/tree.v) | Proof binding, tree identity |
| `hash_pair_collision_resistant` | [simulations/tree.v](../simulations/tree.v) | Internal node uniqueness, Merkle proofs |
| `hash_stem_collision_resistant` | [simulations/tree.v](../simulations/tree.v) | Stem node uniqueness |

**What breaks if violated:**
- Attacker could forge Merkle proofs
- Two different trees could have the same root hash
- State transitions could be falsified

### Preimage Resistance

| Axiom | Location | Dependents |
|-------|----------|------------|
| `hash_value_second_preimage` | [simulations/crypto.v](../simulations/crypto.v) | Cannot find different value with same hash |
| `hash_value_nonzero` | [simulations/tree.v](../simulations/tree.v) | Non-zero values have non-zero hashes |

**What breaks if violated:**
- Attacker could substitute values in proofs
- Sparse tree optimization could fail

### Zero Hash Design Choice

| Axiom | Location | Dependents |
|-------|----------|------------|
| `hash_zero_value` | [simulations/tree.v](../simulations/tree.v) | `hash(0) = 0` for sparse optimization |
| `hash_zero_pair` | [simulations/tree.v](../simulations/tree.v) | `hash(0,0) = 0` for empty subtrees |

**What breaks if violated:**
- Empty subtrees would have non-zero hashes
- Memory/witness size would increase

### Verkle Commitment Security

| Axiom | Location | Dependents |
|-------|----------|------------|
| `verkle_open_correct` | [simulations/verkle.v](../simulations/verkle.v) | Honest proofs verify |
| `verkle_binding` | [simulations/verkle.v](../simulations/verkle.v) | Cannot open to two values at same index |
| `verkle_commit_injective` | [simulations/verkle.v](../simulations/verkle.v) | Different values → different commitments |

**What breaks if violated:**
- Verkle proofs could be forged
- State proofs would not bind to actual values

---

## What Is Property-Tested (QuickChick)

Property-based testing using QuickChick provides statistical confidence for properties that are expensive to prove formally or are not yet proven.

### Properties Tested

| Property | Location | Description |
|----------|----------|-------------|
| `prop_get_insert_same` | [proofs/quickchick_tests.v](../proofs/quickchick_tests.v) | `get (insert t k v) k = Some v` |
| `prop_get_insert_other` | [proofs/quickchick_tests.v](../proofs/quickchick_tests.v) | Insert doesn't affect other keys |
| `prop_insert_delete` | [proofs/quickchick_tests.v](../proofs/quickchick_tests.v) | Delete after insert returns None |
| `prop_insert_idempotent` | [proofs/quickchick_tests.v](../proofs/quickchick_tests.v) | Double insert is idempotent |
| `prop_empty_get` | [proofs/quickchick_tests.v](../proofs/quickchick_tests.v) | Empty tree get returns None |

### Coverage and Confidence

- **Test configuration**: Random trees up to depth 5, random keys from full 32-byte space
- **Sample size**: 10,000 tests per property (5 properties, 50,000 total tests)
- **Known limitations**: Tests use simplified tree generators; edge cases may have lower coverage
- **Relationship to proofs**: All tested properties now have complete formal proofs
- **Status**: All 5 properties passing with 10k tests each

### Running Tests

```bash
# Install QuickChick
opam install coq-quickchick

# Run property tests (when QuickChick is enabled)
coqc -Q specs UBT.Specs -Q simulations UBT.Sim -Q proofs UBT.Proofs proofs/quickchick_tests.v
```

---

## What Is Out of Scope

The following aspects are explicitly **not** verified by this project:

### Performance / Gas Costs

- Time complexity of operations is not proven
- Memory allocation patterns are abstracted
- Gas consumption for EVM execution is not modeled
- Witness size optimization is not verified

**Rationale:** Performance is a separate concern from correctness. The Rust implementation is benchmarked empirically.

### Side-Channel Attacks

- Timing attacks are not considered
- Cache behavior is not modeled
- Power analysis is not relevant
- Memory access patterns are abstracted

**Rationale:** Side-channel resistance requires different verification techniques (e.g., ct-verif) and is outside the scope of functional correctness.

### Concurrency

- Multi-threaded access is not modeled
- Lock-free algorithms are not verified
- Race conditions are not analyzed

**Rationale:** The UBT implementation is designed for single-threaded use within the EVM execution context.

### Storage Backend Correctness

- Database persistence is not verified
- Serialization/deserialization is not proven
- Disk I/O errors are not modeled
- Cache eviction policies are not verified

**Rationale:** Storage is a separate layer. The formal model assumes a reliable key-value store.

### Network Protocol

- P2P gossip is not modeled
- Consensus integration is not verified
- Block propagation is out of scope
- Network partition handling is not modeled

**Rationale:** UBT is a data structure library, not a network protocol.

### Iterator Implementations

- Iterator correctness is not formally proven
- Iteration order guarantees are not verified

**Rationale:** Iterators are primarily for debugging/inspection, not consensus-critical paths.

### Error Message Content

- Error string contents are not verified
- Error categorization is not formalized

**Rationale:** Error handling paths are trusted; formal verification focuses on success paths.

---

## Trust Assumptions

### Rocq/Coq Soundness

**Assumption:** The Rocq proof assistant correctly implements its type theory and the proofs it accepts are valid.

**What if violated:** All proven theorems would be suspect.

**Mitigation:**
- Rocq has decades of development and formal metatheory
- Multiple independent implementations exist (coqchk)
- Critical proofs can be independently checked
- Rocq's kernel is small (~10K lines) and well-audited

### Extraction Correctness

**Assumption:** Rocq's extraction mechanism correctly translates proven code to OCaml/Haskell.

**What if violated:** Extracted code might not preserve proven properties.

**Mitigation:**
- We use manual Rust implementation verified via linking, not extraction
- The linking layer proves simulation ≈ translation
- Property-based testing validates extracted behavior

### rocq-of-rust Translation

**Assumption:** The rocq-of-rust tool correctly translates Rust code to equivalent Rocq terms.

**What if violated:** The translation might not preserve Rust semantics; proofs about translated code wouldn't apply to actual Rust.

**Mitigation:**
- Translation is deterministic and reproducible
- Linking layer explicitly bridges translation and simulation
- Differential testing can compare Rust and simulation behavior
- Translation compiles successfully (syntax is valid)

### Hash Function Implementation

**Assumption:** The concrete hash functions (SHA256, Blake3, Keccak256) correctly implement their specifications.

**What if violated:** Collision resistance and other properties would fail.

**Mitigation:**
- Use well-audited libraries (sha2, blake3 crates)
- Standard test vectors validate implementation
- Multiple hasher backends can be substituted

### Rust Compiler Correctness

**Assumption:** rustc correctly compiles Rust source to machine code.

**What if violated:** Compiled code might not match source semantics.

**Mitigation:**
- rustc is widely used and tested
- Multiple backend targets (LLVM, Cranelift) provide validation
- MIR-based verification tools exist (Miri, Kani)
- Debug and release builds can be compared

### Alloy Primitives Library

**Assumption:** alloy-primitives types (B256, FixedBytes) behave correctly.

**What if violated:** Basic byte operations might be incorrect.

**Mitigation:**
- alloy-primitives is widely used in Ethereum ecosystem
- Extensive test suite exists
- Simple wrapper types with minimal logic

---

## Risk Assessment

### Critical Risks (Breaks Soundness)

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Hash collision found | Very Low | Critical | Use standard hash functions; can upgrade hash algorithm |
| Verkle binding broken | Very Low | Critical | Polynomial commitment schemes have strong proofs |
| Rocq soundness bug | Extremely Low | Critical | Use coqchk; Rocq metatheory is well-studied |

### High Risks (Breaks Linking)

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| rocq-of-rust translation error | Low | High | Differential testing; multiple translations |
| Linking layer gap | Medium | High | Complete admits; add more linking theorems |
| RocqOfRust library bug | Low | High | Test library semantics; upstream fixes |

### Medium Risks (Incomplete Proofs)

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Admitted proofs are false | Medium | Medium | Complete admits; add QuickChick tests |
| Specification axioms wrong | Low | Medium | Review specs against EIP; property testing |
| Edge cases unhandled | Medium | Medium | Expand test coverage; fuzzing |

### Low Risks (Operational)

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Rust stdlib bug | Very Low | Low | Use stable Rust; minimal dependencies |
| Serialization error | Low | Low | Test serialization round-trips |
| Hasher implementation bug | Very Low | Low | Test vectors; multiple implementations |

---

## Verification Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        VERIFICATION SCOPE                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │                    FORMALLY VERIFIED                              │  │
│  │  • Core operations (get, insert, delete)           Complete     │  │
│  │  • Merkle proof soundness/completeness             Complete     │  │
│  │  • State diff correctness                          Complete     │  │
│  │  • EIP-7864 co-location                            Complete     │  │
│  │  • Well-formedness preservation                    Complete     │  │
│  │  • Order independence (all cases)                  Complete     │  │
│  │  • Game-based security (simulations/security.v)    Complete     │  │
│  │    - EUF-MPA, accumulator soundness, advantage bounds            │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                              ↓                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │               CRYPTOGRAPHIC ASSUMPTIONS                           │  │
│  │  • Collision resistance (hash_value, hash_pair, hash_stem)       │  │
│  │  • Preimage resistance                                           │  │
│  │  • Verkle binding/hiding                                         │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                              ↓                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │                   PROPERTY TESTED (QuickChick)                    │  │
│  │  • 5 properties, 10k tests each (50k total, all passing)         │  │
│  │  • Edge cases in order independence                              │  │
│  │  • Random tree operations                                        │  │
│  │  • Stem equality transitivity                                    │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                              ↓                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │                  TRUST ASSUMPTIONS                                │  │
│  │  • Rocq soundness                                                │  │
│  │  • rocq-of-rust correctness                                      │  │
│  │  • Hash implementation                                           │  │
│  │  • Rust compiler                                                 │  │
│  │  • FFI bridge layer (docs/FFI_INTEGRATION.md)      Created      │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                         OUT OF SCOPE                                    │
│  Performance • Side-channels • Concurrency • Storage • Network         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## References

- [EIP-7864 Specification](https://eips.ethereum.org/EIPS/eip-7864)
- [Axiom Audit](axiom_audit.md) - Detailed audit of all axioms
- [Verification Status](VERIFICATION_STATUS.md) - Current proof status
- [rocq-of-rust](https://github.com/formal-land/rocq-of-rust) - Translation tool
- [QuickChick](https://github.com/QuickChick/QuickChick) - Property-based testing
