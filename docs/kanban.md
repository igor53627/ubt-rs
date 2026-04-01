# UBT Maintenance & Best Practices Kanban

> For detailed task breakdowns and ecosystem tracking, see [backlog.md](./backlog.md)

## Backlog

See [backlog.md](./backlog.md) for prioritized action items.

---

## In Progress

_Empty_

---

## Done

### [BK-01] Fix clippy warnings (needless_raw_string_hashes)
**Priority:** High  
Fixed clippy `needless_raw_string_hashes` warnings in `tests/simulation/metrics.rs` by removing unnecessary `#` characters from raw string literals.

### [BK-02] Review and update dependencies
**Priority:** High  
Updated dependencies via `cargo update`. Key updates: `blake3` 1.8.3→1.8.4, `alloy-primitives` 1.5.4→1.5.7. All tests pass.

### [BK-03] Add cargo-deny to CI
**Priority:** Medium  
Added `deny.toml` configuration and cargo-deny CI job for security advisory checking, license compliance, and duplicate dependency detection.

---

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

Declared the crate MSRV via `rust-version` to make compatibility explicit and prevent accidental use of newer language features (current MSRV: Rust 1.85; see KB-10).

---

### [KB-04] Replace unwrap() with expect() in production code
**Priority:** Low
**Files:** `src/tree/hash.rs`

Replaced the two `unwrap()` calls in `incremental_hash_update` with `.expect(...)` to document the cache invariant.

---

### [KB-05] Add #[must_use] to key public APIs
**Priority:** Low
**Files:** `src/tree/mod.rs`, `src/tree/hash.rs`, `src/proof.rs`, `src/streaming.rs`

Added `#[must_use]` to key API functions to discourage accidentally ignoring results like `root_hash()`, `get()`, `generate_stem_proof()`, and streaming root-hash builders.

---

### [KB-06] Add rustfmt.toml
**Priority:** Low
**Files:** `rustfmt.toml`

Pinned basic rustfmt configuration to reduce formatting churn.

---

### [KB-07] Enable pedantic clippy lints
**Priority:** Low
**Files:** `Cargo.toml`

Enabled `clippy::pedantic` lints (warn-level) in `Cargo.toml` with a small allow-list to keep the signal reasonable.

---

### [KB-08] Add release profile optimizations
**Priority:** Low
**Files:** `Cargo.toml`

Added release profile settings (`lto = "thin"`, `codegen-units = 1`) to improve release build performance.

---

### [KB-09] Clean up Cargo.lock in .gitignore
**Priority:** Low
**Files:** `.gitignore`

Removed the `Cargo.lock` entry from `.gitignore` since it is committed.

---

### [KB-10] Align MSRV with dependency requirements
**Priority:** Medium
**Files:** `Cargo.toml`

Updated `rust-version` to `1.85` to reflect current dependency requirements (the dependency graph includes edition 2024 crates such as `alloy-primitives` and `blake3`, which require Rust 1.85+), keeping the declared MSRV accurate.
