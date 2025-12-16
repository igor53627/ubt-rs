# Formal Verification Build Status

Generated: December 2024

## Build Summary

| Target | Status | Notes |
|--------|--------|-------|
| `make proofs-core` | [PASS] | All core proofs compile |
| `make quickchick` | [PASS] | Property tests pass |
| Rocq 9.x Warnings | [CLEAN] | No `deprecated-from-Coq` warnings |

## File-by-File Status

### formal/linking/ (8 files)

| File | Compiles | Admitted | Notes |
|------|----------|----------|-------|
| types.v | [PASS] | 0 | Rocq 9.x injection helpers included |
| operations.v | [PASS] | 0 | Core operation axioms |
| interpreter.v | [PASS] | 0 | M monad interpreter |
| get_stepping.v | [PASS] | 0 | Get operation derivation |
| insert_stepping.v | [PASS] | 0 | Insert operation derivation |
| iterator_stepping.v | [PASS] | 0 | Complete |
| root_hash_stepping.v | [PASS] | 0 | Root hash derivation |
| axiom_elimination.v | [PASS] | 0 | Complete |

### formal/simulations/ (10 files)

| File | Compiles | Notes |
|------|----------|-------|
| crypto.v | [PASS] | Hash primitives |
| tree.v | [PASS] | Core tree operations (Nat.* deprecation warnings only) |
| iterator.v | [PASS] | Iterator semantics |
| security.v | [PASS] | Security properties |
| serialization.v | [PASS] | Serialization proofs |
| streaming.v | [PASS] | Streaming tree builder |
| complexity.v | [PASS] | Complexity bounds |
| tree_build_stepping.v | [PASS] | Tree construction |
| verkle.v | [PASS] | Verkle tree types |
| verkle_linking.v | [PASS] | Verkle linking |

### formal/specs/ (4 files)

| File | Compiles | Notes |
|------|----------|-------|
| tree_spec.v | [PASS] | Tree specification |
| embedding_spec.v | [PASS] | EIP-7864 embedding |
| complexity_spec.v | [PASS] | Complexity specification |
| serialization_spec.v | [PASS] | Serialization spec |

### formal/proofs/ (4 files)

| File | Compiles | Admitted | Notes |
|------|----------|----------|-------|
| correctness.v | [PASS] | 0 | Correctness theorems |
| multiproof.v | [PASS] | 0 | Multiproof verification |
| quickchick_tests.v | [PASS] | 0 | Property tests |
| quickchick_tests_ci.v | [PASS] | 0 | CI property tests |

## Rocq 9.x Compatibility

### Fixed Issues

1. **Import Statements**: All `Require Import Coq.*` migrated to `From Stdlib Require Import *`
2. **Injection Tactic**: `InjectionHelpers` module added in types.v with:
   - `injection H as H1 H2` syntax (new Rocq 9 style)
   - Helper lemmas for Value.t constructors

### Remaining Minor Warnings

- `Nat.add_mod`, `Nat.mod_mul`, `Nat.mod_mod` deprecated in tree.v (line ~1304-1307)
  - These are in proof tactics, not definitions
  - Does not affect proof validity

## Admitted Proof Summary

| Category | Count | Status |
|----------|-------|--------|
| formal/linking/ | 0 | All complete |
| formal/simulations/ | 0 | All complete |
| formal/proofs/ | 0 | All complete |
| formal/specs/ | 3 | Design specification |
| formal/src/ | 79 | RocqOfRust generated (expected) |
| **Total** | **82** | 79 in RocqOfRust src/, rest in specs |

### Admitted in linking/simulations/proofs (0 total)

All proofs in the core verification layers are complete.

The 82 Admitted proofs are in:
- **formal/src/** (79): RocqOfRust auto-generated code (expected)
- **formal/specs/** (3): Design specification axioms

## Axiom/Parameter Count

| File | Axioms + Parameters |
|------|---------------------|
| operations.v | 35 |
| interpreter.v | 51 |
| iterator_stepping.v | 9 |
| axiom_elimination.v | 4 |
| root_hash_stepping.v | 3 |
| get_stepping.v | 2 |
| insert_stepping.v | 1 |
| **Total** | **155** |

See `formal/docs/AXIOM_CATALOG.md` for detailed classification.

## How to Build

```bash
# Sync and build
./scripts/remote-build.sh sync
./scripts/remote-build.sh proofs

# Or locally with Rocq 9.x
cd formal
eval "$(opam env --switch=rocq-9)"
make proofs-core
```
