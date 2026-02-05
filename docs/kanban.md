# UBT Maintenance & Best Practices Kanban

## Backlog

### [KB-04] Replace unwrap() with expect() in production code
**Priority:** Low
**Files:** `src/tree/hash.rs`

Two `unwrap()` calls in `incremental_hash_update` after `contains_key()` checks. Replace with `.expect("cache entry guaranteed by contains_key check")` to document the invariant.

---

### [KB-05] Add #[must_use] to key public APIs
**Priority:** Low
**Files:** `src/tree/mod.rs`, `src/tree/hash.rs`, `src/proof.rs`, `src/streaming.rs`

Functions like `root_hash()`, `get()`, `generate_proof()`, `build_root_hash()` return values that should not be silently discarded. Add `#[must_use]` annotations.

---

### [KB-06] Add rustfmt.toml
**Priority:** Low
**Files:** `rustfmt.toml` (new)

Pin formatting conventions to prevent churn across Rust edition changes:
```toml
edition = "2021"
max_width = 100
```

---

### [KB-07] Enable pedantic clippy lints
**Priority:** Low
**Files:** `Cargo.toml`

Add `[lints.clippy]` section with pedantic warnings and selective allows:
```toml
[lints.clippy]
pedantic = { level = "warn", priority = -1 }
module_name_repetitions = "allow"
must_use_candidate = "allow"
```

---

### [KB-08] Add release profile optimizations
**Priority:** Low
**Files:** `Cargo.toml`

Add for main crate:
```toml
[profile.release]
lto = "thin"
codegen-units = 1
```

---

### [KB-09] Clean up Cargo.lock in .gitignore
**Priority:** Low
**Files:** `.gitignore`

`Cargo.lock` is committed but also listed in `.gitignore`. Remove the `Cargo.lock` line from `.gitignore` since the project ships binaries and benefits from reproducible builds.

---

## In Progress

_Empty_

---

## Done

### [KB-01] Convert tree-depth panics to Result returns
**Priority:** Medium
**Files:** `src/tree/mod.rs`, `src/tree/hash.rs`, `src/tree/build.rs`, `src/streaming.rs`, `src/error.rs`

Converted tree-depth `panic!`s on public code paths into `Result` returns by introducing `UbtError::TreeDepthExceeded { depth }` and propagating errors through `root_hash()` and streaming root-hash builders.

---

### [KB-02] Split tree.rs into submodules
**Priority:** Medium
**Files:** `src/tree/mod.rs`, `src/tree/hash.rs`, `src/tree/build.rs`

Split the `UnifiedBinaryTree` implementation into focused submodules for API surface (`mod.rs`), hashing and rebuild logic (`hash.rs`), and tree-shape construction (`build.rs`), with public API unchanged.

---

### [KB-03] Declare MSRV in Cargo.toml
**Priority:** Medium
**Files:** `Cargo.toml`

Declared the crate MSRV via `rust-version` to make compatibility explicit and prevent accidental use of newer language features.
