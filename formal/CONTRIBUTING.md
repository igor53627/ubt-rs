# Contributing to UBT Formal Verification

## Prerequisites

- **Rocq 9.x** via opam switch `rocq-9`
- **RocqOfRust library** (for linking layer)
- See [INSTALL.md](INSTALL.md) for detailed setup

## CI Requirements

All PRs must pass CI checks before merging:

### Proof Verification (`proofs.yml`)

Runs the full verification pipeline:

| Step | Command | Description |
|------|---------|-------------|
| Core proofs | `make all` | Compile specs, simulations, proofs |
| Linking layer | `make linking` | Compile linking with RocqOfRust |
| OCaml extraction | `make extract` | Generate and verify extracted.ml |
| Documentation | `make docs` | Generate coqdoc HTML |
| Audit | `make audit` | Count axioms/admits |
| Threshold check | `make check-admits` | Fail if admits exceed threshold |

### Proof Lint (`lint.yml`)

Monitors proof quality metrics:

| Metric | Description | Policy |
|--------|-------------|--------|
| `Admitted.` | Incomplete proofs | Warn if count increases |
| `Axiom` | Axiom declarations | Error if count increases (requires justification) |
| `admit.` | Admit tactics | **Fail if present** in `proofs/` or `linking/` |

**Important**: The linter will **fail your PR** if you add `admit.` tactics to `proofs/` or `linking/` directories. Use `Admitted.` with a TODO comment instead.

## Local Development

```bash
# Activate Rocq environment
eval $(opam env --switch=rocq-9)

# Build all proofs
make all

# Build with linking layer (requires RocqOfRust)
make linking

# Run the same checks CI runs
make ci

# Full CI with extraction, docs, and all checks
make ci-full

# Run audit to check axiom/admit counts
make audit

# List all axioms with locations
make verify-axioms

# Check admits against threshold
make check-admits
```

## Before Submitting a PR

Run the CI locally to catch issues:

```bash
eval $(opam env --switch=rocq-9)

# Quick check
make ci

# Or full verification (takes longer)
make ci-full
```

## Proof Guidelines

### Do NOT use in final proofs:
- `admit.` tactic - use `Admitted.` if proof is incomplete
- `Axiom` without justification - document why it's needed

### Acceptable axioms:
- Cryptographic primitives (hash functions)
- Decidability assumptions for types
- Well-documented mathematical assumptions

### Before submitting:
1. Run `make ci` and ensure it passes
2. Run `make audit` and review output
3. Document any new axioms in comments
4. Update README if proof status changes

## Makefile Targets

### Build Targets

| Target | Description |
|--------|-------------|
| `make all` | Build specs, simulations, proofs |
| `make specs` | Build specification files only |
| `make simulations` | Build simulation files |
| `make proofs` | Build proof files |
| `make linking` | Build linking layer (requires RocqOfRust) |
| `make translation` | Build translated Rust code |
| `make extract` | Extract to OCaml |
| `make docs` | Generate HTML documentation |

### CI Targets

| Target | Description |
|--------|-------------|
| `make ci` | CI build: clean + all + linking |
| `make ci-full` | Full CI: ci + extract + docs + audit + check-admits |
| `make audit` | Count axioms/admits, generate report |
| `make verify-axioms` | List all axioms with locations |
| `make check-admits` | Fail if admits exceed threshold |

### Utility Targets

| Target | Description |
|--------|-------------|
| `make clean` | Remove all compiled files |
| `make check-deps` | Verify dependencies are installed |
| `make help` | Show all available targets |

## Axiom Tracking

The current axiom count can be found by running:

```bash
./scripts/count_axioms.sh
```

Or for a formatted report:

```bash
make verify-axioms
```

### Expected Axioms (documented and intentional)

- `hash_value` / `hash_pair` - SHA256 cannot be reasoned about
- `hash_zero_value` / `hash_zero_pair` - Properties of zero hashing
- Decidability for stem/key equality

### Adding New Axioms

If you need to add a new axiom:

1. Document it with a comment explaining why it's necessary
2. Update this section if it's a fundamental assumption
3. Be prepared to justify it in PR review

## Reporting Issues

When reporting proof issues:
1. Include the error message from `coqc`
2. Note which file and line number
3. Include your Rocq version (`coqc --version`)
4. Run `make check-deps` and include output
