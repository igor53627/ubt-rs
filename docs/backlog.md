# UBT Development Backlog

This file tracks recommended priority actions for the UBT (Unified Binary Tree) implementation based on best practices analysis and ecosystem developments.

---

## High Priority

### [BK-01] Fix clippy warnings (needless_raw_string_hashes)
**Status:** ✅ Done (2026-03-31)  
**Files:** `tests/simulation/metrics.rs:102`, `tests/simulation/metrics.rs:338`  
**Effort:** Small  

**Description:**  
Clippy warns about unnecessary `#` characters around raw string literals. The `r#"..."#` format should be changed to `r"..."` since there are no `"` characters inside the strings that would need escaping.

**Acceptance Criteria:**
- [ ] `cargo clippy --all-features` passes without warnings
- [ ] No functional changes to output

---

### [BK-02] Review and update dependencies
**Status:** ✅ Done (2026-03-31)  
**Files:** `Cargo.toml`, `Cargo.lock`  
**Effort:** Medium  
**Risk:** Medium (API changes possible)

**Description:**  
Several dependencies have updates available that may include bug fixes or performance improvements:

| Dependency | Current | Latest | Notes |
|------------|---------|--------|-------|
| `blake3` | 1.5 | 1.8+ | Bug fixes, performance improvements |
| `alloy-primitives` | 1 | 1.5+ | Check for API changes |
| `serde` | 1.0 | 1.0.2xx | Usually safe |
| `thiserror` | 2 | 2.0.x | Patch updates |
| `rand` (dev) | 0.8 | 0.9 | Significant changes - evaluate carefully |
| `proptest` (dev) | 1.4 | 1.6 | Usually safe |

**Acceptance Criteria:**
- [ ] All tests pass after updates
- [ ] Benchmarks show no regressions
- [ ] MSRV compatibility maintained

---

## Medium Priority

### [BK-03] Add cargo-deny to CI for supply chain security
**Status:** ✅ Done (2026-03-31)  
**Files:** `.github/workflows/rust.yml`, `deny.toml` (new)  
**Effort:** Small  

**Description:**  
Add `cargo-deny` to CI pipeline to check for:
- Security vulnerabilities in dependencies
- License compliance
- Banned/duplicate dependencies
- Yanked crate versions

**Acceptance Criteria:**
- [ ] `cargo-deny check` passes locally
- [ ] CI job added and passing
- [ ] `deny.toml` configured with appropriate policies

---

### [BK-04] Add performance benchmarks to CI
**Status:** Open  
**Files:** `.github/workflows/rust.yml`, `benches/`  
**Effort:** Medium  

**Description:**  
Add criterion benchmarks to CI to track performance regressions. Consider using `cargo-criterion` and storing baseline results.

**Acceptance Criteria:**
- [ ] Benchmarks run in CI (not blocking, for tracking)
- [ ] Results uploaded as artifacts
- [ ] Optional: comparison with previous run

---

### [BK-05] Complete Z scopes fix in tree_build_stepping.v
**Status:** Open  
**Files:** `formal/simulations/tree_build_stepping.v:757`  
**Effort:** Medium  
**Type:** Formal verification  

**Description:**  
There's a TODO comment about fixing Z scopes throughout bit-level proofs. This is in the Rocq formal verification code.

**Acceptance Criteria:**
- [ ] Z scopes fixed throughout bit-level proofs
- [ ] All formal proofs still pass
- [ ] TODO comment removed

---

## Low Priority

### [BK-06] Add cargo-machete to CI
**Status:** Open  
**Files:** `.github/workflows/rust.yml`  
**Effort:** Small  

**Description:**  
Add `cargo-machete` to CI to detect unused dependencies and keep the dependency graph lean.

**Acceptance Criteria:**
- [ ] `cargo-machete` CI job added
- [ ] Any detected unused dependencies removed or justified

---

### [BK-07] Fix dead code warnings in simulation tests
**Status:** Open  
**Files:** `tests/simulation/workload.rs`, `tests/simulation/metrics.rs`  
**Effort:** Small  

**Description:**  
Address dead code warnings for unused fields (`key_space_size`, `seed`) and methods (`count`, `new`). Either use them or mark with `#[allow(dead_code)]` with justification.

**Acceptance Criteria:**
- [ ] `cargo check --all-features` shows no dead code warnings
- [ ] Justification comments added where `#[allow(dead_code)]` is used

---

### [BK-08] Review unwrap()/expect() in production code
**Status:** Open  
**Files:** `src/` (various)  
**Effort:** Medium  

**Description:**  
There are ~100 occurrences of panic-related patterns across the codebase. Most are in tests, but review production code paths for any `unwrap()` or `expect()` that could be converted to proper error handling with `?`.

**Acceptance Criteria:**
- [ ] Production code reviewed for unnecessary panics
- [ ] Where possible, convert to `Result` propagation
- [ ] Document invariants where `expect()` is justified

---

### [BK-09] Enable parallel threshold optimization
**Status:** Open  
**Files:** `src/tree/hash.rs`  
**Effort:** Medium  

**Description:**  
Consider adding a minimum stem count threshold before using rayon parallelization. Rayon's overhead may hurt performance for small trees.

**Acceptance Criteria:**
- [ ] Benchmark to determine optimal threshold
- [ ] Implement threshold check before parallel execution
- [ ] Document threshold choice

---

### [BK-10] Complete interpreter stepping TODO
**Status:** Open  
**Files:** `formal/linking/interpreter.v:2273`  
**Effort:** Unknown (depends on Step.step implementation)  
**Type:** Formal verification  

**Description:**  
TODO to enable evaluation lemma when `Step.step` is fully implemented. This is blocked on the M monad interpreter.

**Acceptance Criteria:**
- [ ] `Step.step` fully implemented
- [ ] Lemma enabled and proven
- [ ] TODO removed

---

## Ecosystem Tracking

### Geth Implementation Status (as of March 2026)

**Recent Developments:**

1. **Vitalik Buterin's March 2026 Proposal**  
   - EIP-7864 highlighted as part of Ethereum's "two-track overhaul"
   - Proposal emphasizes replacing hexary Keccak MPT with binary tree
   - Two hash function candidates: BLAKE3 (stable) and Poseidon (3x-100x faster but needs security review)
   - Verkle Trees effectively superseded by binary tree approach due to quantum computing concerns

2. **EIP-7864 Status**  
   - Draft status since January 2025
   - Credited primarily to Guillaume Ballet
   - Main blocker: Finding secure cryptographic hash function with viable proving throughput
   - Target: L1 SNARKification

3. **Key Design Decisions**  
   - **Non-sparse tree** chosen over Sparse Merkle Tree to avoid complex extension nodes
   - **BLAKE3** currently used for easy experimentation
   - **Poseidon2** could re-open sparse tree discussion if proven secure
   - State conversion strategy (EIP-7748) is tree-agnostic

4. **Open Questions in Geth/EL Implementation:**
   - Sync algorithm design for binary tree (critical for adoption)
   - Gas remodeling (EIP-4762) needs constant adjustments
   - In-circuit performance benchmarks ongoing

**Implications for ubt-rs:**
- [ ] Monitor Geth's hash function decision - may need to update default hasher
- [ ] Track sync algorithm developments - may inform API changes
- [ ] Consider adding Poseidon2 hasher (feature-gated) for testing
- [ ] Keep compatibility with Geth's key derivation algorithm (recently fixed in #69)

---

## Changelog

| Date | Action |
|------|--------|
| 2026-03-31 | Backlog created with priority actions from best practices analysis |

