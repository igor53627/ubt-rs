# Installing Dependencies for UBT Formal Verification

This guide covers setting up the formal verification environment for the UBT crate.

## Quick Start

```bash
# 1. Activate the opam switch with Rocq 9.x
eval $(opam env --switch=rocq-9)

# 2. Build all proofs
cd formal
make

# 3. Build translated Rust code (optional)
make translation
```

## Current State

| Layer | Status | Description |
|-------|--------|-------------|
| **specs/** | Complete | Mathematical specifications |
| **simulations/** | Complete | Idiomatic Rocq tree operations |
| **proofs/** | Complete | Correctness proofs at simulation level |
| **src/** | Compiles | rocq-of-rust translation (24,556 lines) |
| **linking/** | Complete | Translation-simulation equivalence |

## Full Installation

### Prerequisites

- **Rust**: nightly-2024-12-07 (for rocq-of-rust translation)
- **opam**: OCaml package manager

### Step 1: Create opam Switch with Rocq 9.x

```bash
# Create new switch
opam switch create rocq-9 ocaml.5.2.0

# Activate it
eval $(opam env --switch=rocq-9)

# Add Coq repository
opam repo add coq-released https://coq.inria.fr/opam/released
```

### Step 2: Install Rocq and Dependencies

```bash
# Install Rocq stdlib
opam install rocq-stdlib -y

# Install hammer tactics (for RocqOfRust)
opam install coq-hammer-tactics -y

# Install coqutil
opam install coq-coqutil -y

# Install smpl
opam install rocq-smpl -y
```

### Step 3: Build RocqOfRust Library

```bash
# Clone if you haven't
git clone https://github.com/formal-land/rocq-of-rust.git ~/pse/paradigm/rocq-of-rust

# Build the library
cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
eval $(opam env --switch=rocq-9)
make -j4
```

This compiles ~200 files and takes a few minutes.

### Step 4: Install rocq-of-rust (for translation)

```bash
cd ~/pse/paradigm/rocq-of-rust

# Install required Rust toolchain
rustup install nightly-2024-12-07
rustup component add rustc-dev --toolchain nightly-2024-12-07

# Install the translator
cargo +nightly-2024-12-07 install --path lib/
```

### Step 5: Build UBT Proofs

```bash
cd /path/to/ubt/formal

# Check dependencies
eval $(opam env --switch=rocq-9)
make check-deps

# Build everything
make all         # specs, simulations, proofs
make translation # translated Rust code
```

## Build Targets

| Target | Description |
|--------|-------------|
| `make` or `make all` | Build specs, simulations, and proofs |
| `make specs` | Build specification files only |
| `make simulations` | Build simulation layer |
| `make proofs` | Build correctness proofs |
| `make translation` | Build translated Rust code (requires RocqOfRust) |
| `make linking` | Build linking layer (requires RocqOfRust) |
| `make translate` | Re-translate Rust to Rocq |
| `make ci` | Full CI build: clean + all + linking |
| `make clean` | Remove all generated files |
| `make check-deps` | Verify installation |

For linking layer setup details, see [docs/LINKING_LAYER_SETUP.md](docs/LINKING_LAYER_SETUP.md).

## Verifying Installation

```bash
$ eval $(opam env --switch=rocq-9)
$ make check-deps

Rocq version: The Rocq Prover, version 9.0.1
compiled with OCaml 5.2.0
RocqOfRust: /Users/user/pse/paradigm/rocq-of-rust/RocqOfRust
RocqOfRust library: compiled
```

## Troubleshooting

### "coqc not found"
```bash
eval $(opam env --switch=rocq-9)
```

### "RocqOfRust library: NOT compiled"
```bash
cd ~/pse/paradigm/rocq-of-rust/RocqOfRust
eval $(opam env --switch=rocq-9)
make
```

### Rust toolchain issues
```bash
rustup install nightly-2024-12-07
rustup component add rustc-dev --toolchain nightly-2024-12-07
```

### Wrong Rocq version
Ensure you're using Rocq 9.x (not Coq 8.x):
```bash
coqc --version  # Should show "Rocq Prover, version 9.x"
```

## File Structure

```
formal/
├── Makefile           # Build automation
├── specs/             # Specifications
│   ├── tree_spec.v
│   └── embedding_spec.v
├── simulations/       # Idiomatic Rocq
│   ├── tree.v
│   ├── crypto.v
│   └── security.v
├── proofs/            # Correctness proofs
│   └── correctness.v
├── linking/           # Translation ↔ Simulation bridge
│   ├── types.v        # Type correspondence (φ encoding)
│   └── operations.v   # Behavioral equivalence
├── src/               # Translation output (auto-generated)
│   ├── tree.v
│   ├── node.v
│   ├── hash.v
│   └── ...
└── docs/              # Documentation
    ├── LINKING_LAYER_SETUP.md  # RocqOfRust setup
    └── SPEC_RUST_LINKAGE.md    # Type/operation mapping
```
