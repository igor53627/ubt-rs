# Linking Layer Setup Guide

This document describes how to set up and build the linking layer that connects the translated Rust code to the simulation-level proofs.

## Overview

The linking layer (`formal/linking/`) establishes behavioral equivalence between:
- **Translated Rust code** (`src/*.v`) - Auto-generated via `rocq-of-rust`
- **Simulation layer** (`simulations/*.v`) - Idiomatic Rocq tree operations

```
┌─────────────────────────────────────────────────────────────┐
│  simulations/tree.v    Pure functional simulation           │
│       ↓ linked via φ encoding                               │
│  linking/types.v       Type correspondence                  │
│  linking/operations.v  Behavioral equivalence               │
│       ↑ requires                                            │
│  src/tree.v            Translated Rust (monadic M monad)    │
│       ↑ requires                                            │
│  RocqOfRust library    M monad, Value.t, trait semantics    │
└─────────────────────────────────────────────────────────────┘
```

## Prerequisites

| Dependency | Version | Purpose |
|------------|---------|---------|
| Rocq | 9.x | Proof assistant (rocq-9 opam switch) |
| RocqOfRust library | Latest | M monad and linking infrastructure |
| rocq-of-rust (optional) | nightly-2024-12-07 | Re-translate Rust to Rocq |

## RocqOfRust Library Setup

The linking layer requires the compiled RocqOfRust library.

### Step 1: Clone RocqOfRust

```bash
# Clone to the expected location
git clone https://github.com/formal-land/rocq-of-rust.git ~/pse/paradigm/rocq-of-rust
```

### Step 2: Build the Library

```bash
cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
eval $(opam env --switch=rocq-9)

# Build all ~200 files (takes a few minutes)
make -j4
```

Verify the build succeeded:
```bash
ls -la M.vo  # Should exist after successful build
```

### Step 3: Configure Path (if non-standard location)

The Makefile expects RocqOfRust at `~/pse/paradigm/rocq-of-rust/RocqOfRust`. To use a different path:

```bash
# Option 1: Set environment variable
export ROCQOFRUST_PATH=/path/to/rocq-of-rust/RocqOfRust

# Option 2: Override in make command
make linking ROCQOFRUST_PATH=/path/to/rocq-of-rust/RocqOfRust
```

Or edit `formal/Makefile` line 8:
```makefile
ROCQOFRUST_PATH := /your/custom/path/RocqOfRust
```

## Building the Linking Layer

### Check Dependencies First

```bash
cd /path/to/ubt/formal
eval $(opam env --switch=rocq-9)
make check-deps
```

Expected output:
```
Rocq version: The Rocq Prover, version 9.0.1
RocqOfRust: /Users/user/pse/paradigm/rocq-of-rust/RocqOfRust
RocqOfRust library: compiled
```

### Build Linking

```bash
# Build simulations first (dependency)
make simulations

# Build translated Rust code (dependency)
make translation

# Build linking layer
make linking
```

Or in one command:
```bash
make ci  # Runs: clean all linking
```

### Error Messages

If RocqOfRust is not found:
```
Error: RocqOfRust not found at /Users/user/pse/paradigm/rocq-of-rust/RocqOfRust
Build it first: cd rocq-of-rust/RocqOfRust && make
```

If RocqOfRust is not compiled:
```
Error: Cannot find library RocqOfRust.M
Solution: cd /path/to/RocqOfRust && make -j4
```

## What the Linking Layer Proves

### Type Linking (`linking/types.v`)

Defines the φ encoding that maps simulation types to Rust `Value.t`:

| Simulation Type | Rust Type | Link Module |
|-----------------|-----------|-------------|
| `Byte` | `u8` | `ByteLink` |
| `Bytes32` | `FixedBytes<32>` | `Bytes32Link` |
| `Stem` | `ubt::key::Stem` | `StemLink` |
| `SubIndex` | `u8` | `SubIndexLink` |
| `TreeKey` | `ubt::key::TreeKey` | `TreeKeyLink` |
| `SimTree` | `UnifiedBinaryTree<H>` | `SimTreeLink` |
| `option A` | `Option<A>` | `OptionLink` |

### Behavioral Equivalence (`linking/operations.v`)

Proves that running translated Rust code produces results equivalent to simulation:

| Theorem | Statement |
|---------|-----------|
| `get_refines` | `rust_get ≈ sim_tree_get` |
| `insert_refines` | `rust_insert ≈ sim_tree_insert` |
| `delete_refines` | `rust_delete ≈ sim_tree_delete` |
| `root_hash_refines` | `rust_root_hash ≈ sim_root_hash` |

### Composition Theorems

| Theorem | Statement |
|---------|-----------|
| `get_after_insert_same` | `get (insert t k v) k = Some v` (when v ≠ 0) |
| `get_after_delete_same` | `get (delete t k) k = None` |
| `insert_insert_comm` | Inserts at different stems commute |
| `batch_preserves_refinement` | Batch operations preserve linking |

## Current Limitations

### Axiomatized Components

The linking layer axiomatizes certain aspects of Rust execution:

| Axiom | Reason |
|-------|--------|
| `Run.run_*` | M monad execution semantics |
| `*_executes` | Full trait resolution not implemented |
| `*_no_panic` | Panic freedom (verified by inspection) |

See `linking/operations.v:Limitations` module for the complete list.

### Future Work

1. **Full M monad interpreter** - Replace `Run.run` axioms with executable semantics
2. **HashMap linking** - Connect Rust HashMap to Rocq StemMap
3. **Trait resolution** - Implement `GetTraitMethod` semantics
4. **Closure verification** - Link iterator closures to fold operations

## CI Integration

### Current CI Target

```bash
make ci  # clean + all + linking
```

This verifies:
1. Specifications compile
2. Simulations compile
3. Proofs compile
4. Translated code compiles
5. Linking compiles

### Optional CI Enhancements

For CI systems that need to build RocqOfRust:

```yaml
# Example GitHub Actions
- name: Cache RocqOfRust
  uses: actions/cache@v3
  with:
    path: ~/pse/paradigm/rocq-of-rust/RocqOfRust
    key: rocqofrust-${{ hashFiles('rocq-of-rust.version') }}

- name: Build RocqOfRust
  run: |
    if [ ! -f ~/pse/paradigm/rocq-of-rust/RocqOfRust/M.vo ]; then
      git clone https://github.com/formal-land/rocq-of-rust.git ~/pse/paradigm/rocq-of-rust
      cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
      make -j4
    fi

- name: Build UBT Linking
  run: |
    cd formal
    make ci
```

### Skipping Linking in CI

If RocqOfRust setup is problematic, skip the linking layer:

```bash
make all  # Builds specs, simulations, proofs only
```

The core verification (simulation-level proofs) is complete without the linking layer.

## Troubleshooting

### "Cannot find library RocqOfRust.M"

```bash
# Ensure RocqOfRust is compiled
cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
eval $(opam env --switch=rocq-9)
make -j4

# Check M.vo exists
ls M.vo
```

### "Wrong Rocq version"

RocqOfRust requires Rocq 9.x:
```bash
# Check version
rocqc --version  # Should show Rocq 9.x

# If using Coq 8.x, switch:
eval $(opam env --switch=rocq-9)
```

### "Unbound module UBT.Sim.tree"

Build simulations first:
```bash
make simulations
```

### "Unbound module src.tree"

Build translation first:
```bash
make translation
```

## File Reference

| File | Lines | Purpose |
|------|-------|---------|
| `linking/types.v` | 212 | Type correspondence (φ encoding) |
| `linking/operations.v` | ~800 | Behavioral equivalence proofs |

## See Also

- [SPEC_RUST_LINKAGE.md](SPEC_RUST_LINKAGE.md) - Detailed type/operation mapping
- [INSTALL.md](../INSTALL.md) - General setup instructions
- [axiom_audit.md](axiom_audit.md) - Axiom tracking
