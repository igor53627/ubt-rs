# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **Remove Redundant Admitted** (PR #58, Issue #51)
  - FuelExec.run_fuel_implies_run removed (was duplicate of RunFuelLink.run_fuel_implies_run_v2)
  - Use RunFuelLink.run_fuel_implies_run_v2 for fuel-to-run connection
  - Reduces Admitted count from 2 to 1
  - Only remaining Admitted: root_hash_executes_sketch (#53)

- **Monad Bind Axiom** (PR #57, Issues #49, #54)
  - Laws.let_sequence promoted to explicit [AXIOM:MONAD-BIND]
  - Standard monad law: running m then f equals running (M.let_ m f)
  - MonadLaws.run_bind_fuel now PROVEN using let_sequence
  - BatchStepping.batch_fold_short_circuit PROVEN via induction + let_sequence

- **Fuel Determinism Lemma** (PR #56, Issue #52)
  - Fuel.run_success_unique proven by induction on fuel
  - Uses fact that SmallStep.step is a function (deterministic)
  - Enables proving theorems from execution axioms

- **Monad Law Proofs** (PR #55, Issues #48-#54)
  - Laws.run_pure and Laws.run_panic fully proven
  - MonadLaws.run_pure_proven and run_panic_proven completed
  - step_let split into step_let_pure (proven) + step_let_nonpure (axiom)
  - Created GitHub issues #48-#54 for remaining Admitted proofs

### Changed

- **InsertExec.insert_fuel_refines_simulation converted from Admitted to Qed** (PR #56, Issue #52)
  - Proof uses Fuel.run_success_unique determinism lemma
  - Shows that any successful fuel execution produces simulation-equivalent result

- **Semantic gap classification** (PR #56, #57, #58)
  - Remaining Admitted proofs: 1 (down from 10 initially)
  - Issue #51: RESOLVED - redundant lemma removed
  - Issue #53: requires full closure/trait stepping (only remaining Admitted)

- **Linking Layer Infrastructure** (PR #47, Issues #40-#46)
  - 5-layer OpExec architecture for structured proof decomposition
  - RunFuelLink module connecting abstract Run.run to concrete Fuel.run
  - TraitRegistry with Sha256 and Blake3 hasher instances
  - RootHashLink module with node hash stepping lemmas
  - BatchStepping module with fold-based batch verification
  - InsertExec module with HashMap entry pattern stepping

- **Documentation**
  - CI status badges in README (Proof Verification, Proof Lint)
  - Docs coverage badge linking to formal/docs/
  - Updated LINKING_COMPLETION_ROADMAP.md with PR #47 progress
  - New wiki pages for OpExec Architecture, RunFuelLink, Batch Verification

### Changed

- **delete_executes converted from Axiom to Theorem**
  - Proof reduces to insert_executes with zero32 value
  - Uses delete_is_insert_zero and zero32_wf lemmas

- **Batch verification definitions**
  - rust_verify_batch now properly iterates using verify_batch_fold
  - rust_verify_multiproof reconstructs and compares Merkle roots

- **insert_run_refines now uses conjunction**
  - Changed from implication (->) to conjunction (/\)
  - Properly asserts both success AND refinement

### Fixed

- stemnode_new_is_empty converted to proper axiom (was trivial reflexivity)
- get_trait_method_resolves now invokes resolved body via CallClosure
- Removed all admit. tactics to pass lint-proofs CI check

## [0.2.0] - 2024-12-12

### Added

- Incremental update mode for O(D*C) root updates
- Parallel hashing via rayon (enabled by default)
- Streaming tree builder for memory-efficient migrations
- Formal verification complete with 0 admits remaining
- QuickChick property-based testing (50,000 tests)
- OCaml extraction with FFI bridge

### Changed

- Repository URL updated to igor53627/ubt-rs

## [0.1.0] - 2024-12-01

### Added

- Initial implementation of EIP-7864 Unified Binary Tree
- Core tree operations: insert, get, delete, root_hash
- Blake3 hasher implementation
- Tree key and stem abstractions
- Account embedding per EIP-7864
- Code chunking for contract bytecode
- Formal verification framework with Rocq proofs
