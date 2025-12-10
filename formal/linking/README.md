# Linking Layer for Rust-to-Rocq Verification

This directory contains the linking layer that establishes behavioral equivalence between translated Rust code and the simulation-level proofs.

## Overview

```text
Rust Code (src/*.rs)
       |
       v  [rocq-of-rust translation]
Translated Rocq (src/*.v)     <-- Monadic M monad code
       |
       v  [linking layer]
Linking (linking/*.v)         <-- Type/behavioral correspondence
       |
       v  [refinement proofs]
Simulation (simulations/*.v)  <-- Pure functional specifications
       |
       v
Specification (specs/*.v)     <-- EIP-7864 requirements
```

## Files

| File | Purpose |
|------|---------|
| `types.v` | Type linking via phi encoding (simulation types -> Rust Value.t) |
| `operations.v` | Behavioral equivalence proofs (rust_* matches sim_*) |
| `interpreter.v` | M monad interpreter for full linking proofs (WIP) |

## Dependencies

**Required:** RocqOfRust library at `~/pse/paradigm/rocq-of-rust/RocqOfRust`

### Setup Instructions

```bash
# 1. Clone RocqOfRust
git clone https://github.com/formal-land/rocq-of-rust.git ~/pse/paradigm/rocq-of-rust

# 2. Build the library (requires Rocq 9.x)
cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
eval $(opam env --switch=rocq-9)
make -j4

# 3. Verify build succeeded
ls M.vo  # Should exist

# 4. Build UBT linking layer
cd /path/to/ubt-rs/formal
make linking
```

**Custom path:** Override with `make linking ROCQOFRUST_PATH=/your/path/RocqOfRust`

## Type Linking (types.v)

Defines the phi encoding that maps simulation types to RocqOfRust `Value.t`:

| Simulation Type | Rust Type | Link Module |
|-----------------|-----------|-------------|
| `Byte` | `u8` | `ByteLink` |
| `Bytes32` | `FixedBytes<32>` | `Bytes32Link` |
| `Stem` | `ubt::key::Stem` | `StemLink` |
| `SubIndex` | `u8` | `SubIndexLink` |
| `TreeKey` | `ubt::key::TreeKey` | `TreeKeyLink` |
| `Value` | `B256` | `ValueLink` |
| `option A` | `Option<A>` | `OptionLink` |
| `SubIndexMap` | `HashMap<u8, B256>` | `SubIndexMapLink` |
| `StemMap` | `HashMap<Stem, StemNode>` | `StemMapLink` |
| `SimTree` | `UnifiedBinaryTree<H>` | `SimTreeLink` |

### Key Concepts

- **phi (encoding):** Maps Rocq simulation values to Rust `Value.t` representation
- **tree_refines:** Refinement relation stating Rust tree equals phi-encoding of simulation tree
- **OfTy.t:** Witnesses type correspondence between Rocq and Rust types

## Behavioral Equivalence (operations.v)

Establishes that running translated Rust code produces results equivalent to simulation:

### Operation Linking Modules

| Module | Axiom | Statement |
|--------|-------|-----------|
| `GetLink` | `get_executes` | `rust_get ≈ sim_tree_get` |
| `InsertLink` | `insert_executes` | `rust_insert ≈ sim_tree_insert` |
| `DeleteLink` | `delete_executes` | `rust_delete ≈ sim_tree_delete` |
| `NewLink` | `new_executes` | `rust_new ≈ empty_tree` |
| `HashLink` | `root_hash_executes` | `rust_root_hash ≈ sim_root_hash` |

### Composition Theorems

| Theorem | Statement |
|---------|-----------|
| `get_after_insert_same` | `get (insert t k v) k = Some v` (when v != 0) |
| `get_after_delete_same` | `get (delete t k) k = None` |
| `insert_insert_comm` | Inserts at different stems commute |
| `batch_preserves_refinement` | Batch operations preserve linking |

## M Monad Interpreter (interpreter.v)

Work-in-progress implementation for converting execution axioms to proven theorems:

### Status

| Component | Status |
|-----------|--------|
| Monad laws (run_pure, run_panic) | **PROVEN** |
| Bind sequencing (run_bind) | Partial |
| Operation execution (*_executes) | Axiom -> WIP |
| HashMap linking | Axiomatized |
| Trait resolution | Skeleton |

### Architecture

```text
SmallStep.step : Config -> StepResult    (single-step evaluation)
       |
       v
Fuel.run : nat -> Config -> Outcome      (bounded multi-step)
       |
       v
FuelExec.run_with_fuel                   (compatibility layer)
```

## Axiom Classification

All axioms are tagged with classification markers:

| Tag | Meaning | Risk |
|-----|---------|------|
| `[AXIOM:MONAD]` | M monad execution semantics | Low |
| `[AXIOM:IMPL-GAP]` | Rust-simulation correspondence | High |
| `[AXIOM:PANIC]` | Panic freedom assertions | Medium |
| `[AXIOM:BATCH]` | Batch verification operations | Medium |
| `[AXIOM:ENCODING]` | phi encoding properties | Low |
| `[AXIOM:HASHMAP]` | HashMap operation semantics | Medium |

See [axiom_audit.md](../docs/axiom_audit.md) for complete axiom tracking.

## Building

```bash
# Build all dependencies first
make simulations
make translation

# Build linking layer
make linking

# Or build everything for CI
make ci
```

## Troubleshooting

### "Cannot find library RocqOfRust.M"

```bash
cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
eval $(opam env --switch=rocq-9)
make -j4
```

### "Unbound module UBT.Sim.tree"

```bash
make simulations
```

### "Unbound module src.tree"

```bash
make translation
```

### Wrong Rocq version

RocqOfRust requires Rocq 9.x:
```bash
rocqc --version  # Should show Rocq 9.x, not Coq 8.x
eval $(opam env --switch=rocq-9)
```

## CI Integration

The linking layer is included in CI builds but skipped if RocqOfRust is not available:

```bash
make ci   # clean + all + linking (requires RocqOfRust)
make all  # specs + simulations + proofs only (no RocqOfRust needed)
```

### Why Skipped in Some CI Environments

- RocqOfRust takes 5-10 minutes to build (~200 files)
- Requires Rocq 9.x and specific opam switch
- Core verification (simulation proofs) is complete without linking

### To Enable in CI

1. Cache RocqOfRust build artifacts
2. Set `ROCQOFRUST_PATH` environment variable
3. Use `make ci` target

See [LINKING_LAYER_SETUP.md](../docs/LINKING_LAYER_SETUP.md) for GitHub Actions example.

## Future Work

1. **Full M monad interpreter** - Replace `*_executes` axioms with proofs
2. **HashMap linking** - Connect Rust HashMap to simulation StemMap
3. **Trait resolution** - Implement `GetTraitMethod` semantics for Hasher
4. **Closure verification** - Link iterator closures to fold operations
5. **Panic freedom proofs** - Verify all `panic!` calls unreachable

## References

- [LINKING_LAYER_SETUP.md](../docs/LINKING_LAYER_SETUP.md) - Detailed setup guide
- [SPEC_RUST_LINKAGE.md](../docs/SPEC_RUST_LINKAGE.md) - Type/operation mapping
- [axiom_audit.md](../docs/axiom_audit.md) - Complete axiom tracking
- [INSTALL.md](../INSTALL.md) - General setup instructions
