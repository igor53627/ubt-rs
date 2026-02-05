# UBT Maintenance & Best Practices Kanban

## Backlog

### [KB-01] Convert tree-depth panics to Result returns
**Priority:** Medium
**Files:** `src/tree.rs`, `src/streaming.rs`, `src/error.rs`

`panic!("Tree depth exceeded maximum of 248 bits")` in public API functions should return `Result` instead. Add `TreeDepthExceeded { depth: usize }` variant to `UbtError`. Update `root_hash()` and related functions to propagate errors.

---

### [KB-02] Split tree.rs into submodules
**Priority:** Medium
**Files:** `src/tree.rs` (1,281 lines)

Split into:
- `src/tree/mod.rs` — struct definition, insert/get/delete
- `src/tree/hash.rs` — root hash strategies (rebuild, cached, incremental)
- `src/tree/build.rs` — sorted-stem tree construction

Public API unchanged.

---

### [KB-03] Declare MSRV in Cargo.toml
**Priority:** Medium
**Files:** `Cargo.toml`

Add `rust-version = "1.74"` (or actual minimum). Prevents accidental use of newer features and gives users clear compatibility info.

---

### [KB-04] Replace unwrap() with expect() in production code
**Priority:** Low
**Files:** `src/tree.rs`

Two `unwrap()` calls in `incremental_hash_update` after `contains_key()` checks. Replace with `.expect("cache entry guaranteed by contains_key check")` to document the invariant.

---

### [KB-05] Add #[must_use] to key public APIs
**Priority:** Low
**Files:** `src/tree.rs`, `src/proof.rs`, `src/streaming.rs`

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

_Empty_
