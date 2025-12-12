# Linking Layer Completion Roadmap

**Created:** December 2024  
**Updated:** December 2024 (PR #58)  
**Status:** Near Complete - 1 Admitted Proof Remaining  
**Owner:** UBT Formal Verification Team

---

## Executive Summary

The linking layer (`formal/linking/`) bridges translated Rust code to simulation-level proofs. This roadmap tracks what's proven, what's axiomatized, and the path to complete verification.

### Current State (Post PR #58)

| Category | Status | Count |
|----------|--------|-------|
| Type Links | **Complete** | 13 types linked |
| Refinement Lemmas | **Proven** | 15 lemmas |
| Execution Axioms | **Partial** | 6 axioms (2 proven: delete_executes, insert_fuel_refines) |
| Panic Freedom | **Axiomatized** | 4 axioms |
| Composition Theorems | **Proven** | 18 theorems |
| Monad Laws | **Complete** | 5 proven, 1 explicit axiom (let_sequence) |
| Batch Verification | **Infrastructure** | 4 axioms, 6 proven lemmas |
| Run/Fuel Connection | **Complete** | 2 axioms, 6 proven lemmas |
| Admitted Proofs | **1 remaining** | root_hash_executes_sketch (#53) |

### Recent Progress (PR #58 - Issue #51)

| Issue | Status | Details |
|-------|--------|---------|
| #51 run_fuel_implies_run | **RESOLVED** | Removed redundant lemma, use RunFuelLink.run_fuel_implies_run_v2 |

### Prior Progress (PR #57 - Issues #49, #54)

| Issue | Status | Details |
|-------|--------|---------|
| #49 Laws.let_sequence | **AXIOM** | Promoted to explicit [AXIOM:MONAD-BIND] |
| #49 MonadLaws.run_bind_fuel | **PROVEN** | Uses let_sequence axiom |
| #54 batch_fold_short_circuit | **PROVEN** | Induction + let_sequence |

### Prior Progress (PR #56 - Issue #52)

| Issue | Status | Details |
|-------|--------|---------|
| #52 insert_fuel_refines | **CLOSED** | Fuel.run_success_unique determinism |
| #53 root_hash_executes_sketch | Semantic Axiom | Only remaining Admitted |

### Prior Progress (PR #55 - Issues #48-#54)

| Issue | Status | Details |
|-------|--------|---------|
| #48 Laws.run_pure/panic | **PROVEN** | Reflexivity after simpl |
| #50 MonadLaws theorems | **PROVEN** | Lifts Laws lemmas |

### Prior Progress (PR #47 - Issues #40-#46)

| Issue | Status | Details |
|-------|--------|---------|
| #41 get_executes | Infrastructure | 5-layer OpExec architecture |
| #42 insert_executes | Infrastructure | InsertExec module with entry stepping |
| #43 delete_executes | **PROVEN** | Reduced to insert with zero32 |
| #44 root_hash_executes | Infrastructure | TraitRegistry + RootHashLink |
| #45 Run.run via Fuel.run | Infrastructure | RunFuelLink module |
| #46 Batch verification | Infrastructure | BatchStepping module |

---

## 1. Current Linking Coverage

### 1.1 Type Linking (Complete)

All core types have φ encodings in `linking/types.v`:

| Simulation Type | Rust Type | Status | Module |
|-----------------|-----------|--------|--------|
| `Byte` | `u8` | ✅ Proven | `ByteLink` |
| `Bytes32` | `FixedBytes<32>` | ✅ Proven | `Bytes32Link` |
| `Bytes31` | `[u8]` | ✅ Proven | `Bytes31Link` |
| `Stem` | `ubt::key::Stem` | ✅ Proven | `StemLink` |
| `SubIndex` | `u8` | ✅ Proven | `SubIndexLink` |
| `TreeKey` | `ubt::key::TreeKey` | ✅ Proven | `TreeKeyLink` |
| `Value` | `B256` | ✅ Proven | `ValueLink` |
| `option A` | `Option<A>` | ✅ Proven | `OptionLink` |
| `T + E` | `Result<T, E>` | ✅ Proven | `ResultLink` |
| `bool` | `bool` | ✅ Proven | `BoolLink` |
| `SubIndexMap` | `HashMap<u8, B256>` | ✅ Proven | `SubIndexMapLink` |
| `StemMap` | `HashMap<Stem, StemNode>` | ✅ Proven | `StemMapLink` |
| `SimTree` | `UnifiedBinaryTree<H>` | ✅ Proven | `SimTreeLink` |

### 1.2 Type Correspondence Lemmas (Complete)

| Lemma | Statement | Status |
|-------|-----------|--------|
| `bytes32_encoding_injective` | φ v1 = φ v2 → v1 = v2 | ✅ Proven |
| `treekey_encoding_preserves_components` | TreeKey encoding structure | ✅ Proven |
| `option_encoding_disjoint` | φ None ≠ φ (Some v) | ✅ Proven |
| `simtree_encoding_preserves_stems` | SimTree encoding structure | ✅ Proven |
| `wf_stem_encoding_length` | Well-formed stem → 31 bytes | ✅ Proven |
| `value_encoding_structure` | Value → FixedBytes<32> | ✅ Proven |

### 1.3 Refinement Relation (Complete)

| Definition/Lemma | Statement | Status |
|------------------|-----------|--------|
| `tree_refines` | rust_tree = φ sim_tree | ✅ Defined |
| `key_refines` | rust_key = φ sim_key | ✅ Defined |
| `value_refines` | rust_val = φ sim_val | ✅ Defined |
| `tree_refines_refl` | Reflexivity | ✅ Proven |
| `key_refines_refl` | Reflexivity | ✅ Proven |
| `value_refines_refl` | Reflexivity | ✅ Proven |

---

## 2. Execution Axioms (Main Gap)

These axioms are the primary verification gap. They require a full M monad interpreter.

### 2.1 Operation Execution Axioms

| Axiom | Location | Risk | Dependencies |
|-------|----------|------|--------------|
| `get_executes` | `operations.v:415` | High | tree_refines, wf_tree, wf_stem |
| `insert_executes` | `operations.v:540` | High | tree_refines, wf_tree, wf_stem, wf_value |
| `delete_executes` | `operations.v:659` | Medium | insert_executes |
| `new_executes` | `operations.v:~750` | Low | empty_tree definition |
| `root_hash_executes` | `operations.v:~830` | High | tree_refines, hash_* axioms |

### 2.2 Monad Execution Axioms

| Axiom | Location | Risk | Notes |
|-------|----------|------|-------|
| `Run.run_pure` | `operations.v:203` | Low | Standard monad law |
| `Run.run_bind` | `operations.v:209` | Low | Standard monad law |
| `Run.run_panic` | `operations.v:225` | Low | Exception semantics |
| `Run.run_eval_sound` | `operations.v:231` | Medium | Step↔run connection |

### 2.3 Panic Freedom Axioms

| Axiom | Location | Risk | Mitigation |
|-------|----------|------|------------|
| `get_no_panic` | `operations.v:~762` | Low | Code inspection |
| `insert_no_panic` | `operations.v:~775` | Low | Code inspection |
| `delete_no_panic` | `operations.v:~791` | Low | Code inspection |
| `root_hash_no_panic` | `operations.v:~805` | Low | Code inspection |

### 2.4 Batch Verification Axioms

| Axiom | Location | Risk | Notes |
|-------|----------|------|-------|
| `rust_verify_batch_inclusion_executes` | `operations.v:~821` | High | Batch proof logic |
| `rust_verify_shared_executes` | `operations.v:~888` | Medium | Optimization variant |

---

## 3. Proven Theorems

### 3.1 Termination Lemmas (All Proven)

| Lemma | Statement |
|-------|-----------|
| `get_terminates` | Get always terminates on wf inputs |
| `insert_terminates` | Insert always terminates on wf inputs |
| `delete_terminates` | Delete always terminates on wf inputs |
| `root_hash_terminates` | Root hash always terminates |

### 3.2 Composition Theorems (All Proven)

| Theorem | Statement |
|---------|-----------|
| `get_after_insert_same` | get (insert t k v) k = Some v |
| `get_after_insert_other_stem` | Different stems → no interference |
| `get_after_insert_other_subindex` | Same stem, different subindex → no interference |
| `get_after_delete_same` | get (delete t k) k = None |
| `insert_insert_comm` | Different stems commute |
| `insert_insert_comm_subindex` | Same stem, different subindex commute |
| `refinement_chain` | Batch operations preserve refinement |
| `batch_preserves_refinement` | Batch ops preserve tree_refines |
| `batch_preserves_wf` | Batch ops preserve wf_tree |

### 3.3 Well-formedness Preservation (All Proven)

| Theorem | Statement |
|---------|-----------|
| `insert_preserves_wf_link` | Insert maintains wf_tree |
| `delete_preserves_wf_link` | Delete maintains wf_tree |
| `zero32_wf` | zero32 is well-formed value |

---

## 4. Remaining Work Items

### 4.1 M Monad Interpreter (Critical Path)

**Location:** `linking/interpreter.v`, `linking/monad.v`  
**Effort:** High (40-60 hours)  
**Dependencies:** RocqOfRust library semantics

| Component | Status | Notes |
|-----------|--------|-------|
| Step relation | Partial | Basic cases implemented |
| Fuel-based execution | Complete | `Fuel.run` implemented |
| Pure/panic handling | Complete | `Laws.run_pure`, `Laws.run_panic` |
| Let binding | Partial | `Laws.let_sequence` admitted |
| Closure semantics | Stub | Needs full implementation |
| Trait resolution | Stub | `TraitRegistry` skeleton |
| State operations | Stub | alloc/read/write stubs |

**Tasks:**
1. Complete `SmallStep.step` for all LowM constructors
2. Implement `TraitRegistry.resolve_method` with actual Hasher impls
3. Prove `Fuel.sufficient_implies_eval`
4. Link `Run.run` axioms to fuel-based execution

### 4.2 HashMap Linking (High Priority)

**Location:** New module needed  
**Effort:** Medium (15-25 hours)  
**Dependencies:** M monad interpreter

Rust's `HashMap<Stem, StemNode>` must be linked to simulation's `StemMap`.

| Task | Status | Notes |
|------|--------|-------|
| HashMap.get stepping | Axiom | `hashmap_get_steps` |
| HashMap.entry stepping | TODO | Needed for insert |
| HashMap.insert stepping | TODO | Alternative to entry |
| SubIndexMap correspondence | Axiom | `subindexmap_get_steps` |

**Proof Strategy:**
1. Define HashMap simulation as association list
2. Prove HashMap.get = assoc list lookup
3. Prove HashMap.insert = assoc list update
4. Connect via StemMap/SubIndexMap links

### 4.3 Closure Semantics (Medium Priority)

**Location:** `linking/interpreter.v:Closure`  
**Effort:** Medium (10-15 hours)  
**Dependencies:** M monad interpreter

| Task | Status | Notes |
|------|--------|-------|
| Closure value extraction | Stub | Type mismatch to fix |
| Closure application | Stub | Needs body execution |
| Captured variable handling | TODO | Environment semantics |

### 4.4 Hasher Trait Linking (Medium Priority)

**Location:** `linking/interpreter.v:TraitRegistry`  
**Effort:** Medium (10-15 hours)  
**Dependencies:** Hash function axioms

| Task | Status | Notes |
|------|--------|-------|
| Register PoseidonHasher | TODO | Populate instances list |
| Register Keccak256Hasher | TODO | Populate instances list |
| Method resolution | Skeleton | find_impl, resolve_method |
| Hash computation correspondence | TODO | Link hash_value, hash_pair |

### 4.5 Panic Analysis Automation (Low Priority)

**Location:** New tooling needed  
**Effort:** Low (5-10 hours)  
**Dependencies:** None

Currently panic freedom is axiomatized based on code inspection. Could be automated:

| Task | Status | Notes |
|------|--------|-------|
| Identify all panic! sites | Manual | See PANIC_ANALYSIS.md |
| Prove unreachability | TODO | Via preconditions |
| Integration test coverage | Partial | Via QuickChick |

---

## 5. Dependency Graph

```
                    ┌─────────────────────────────────────┐
                    │         M MONAD INTERPRETER          │
                    │     (interpreter.v, monad.v)         │
                    └─────────────────┬───────────────────┘
                                      │
           ┌──────────────────────────┼──────────────────────────┐
           │                          │                          │
           ▼                          ▼                          ▼
┌─────────────────────┐  ┌─────────────────────────┐  ┌─────────────────────┐
│  HASHMAP LINKING    │  │   CLOSURE SEMANTICS     │  │   TRAIT REGISTRY    │
│  (new module)       │  │   (interpreter.v)       │  │   (interpreter.v)   │
└──────────┬──────────┘  └───────────┬─────────────┘  └──────────┬──────────┘
           │                         │                           │
           └─────────────────────────┼───────────────────────────┘
                                     │
                                     ▼
                    ┌─────────────────────────────────────┐
                    │     OPERATION EXECUTION PROOFS      │
                    │  (get_executes, insert_executes)    │
                    └─────────────────┬───────────────────┘
                                      │
                                      ▼
                    ┌─────────────────────────────────────┐
                    │        PANIC FREEDOM PROOFS         │
                    │   (*_no_panic → proven theorems)    │
                    └─────────────────────────────────────┘
```

---

## 6. Effort Estimates

### 6.1 By Component

| Component | Effort (hours) | Risk | Priority |
|-----------|----------------|------|----------|
| M monad interpreter | 40-60 | High | Critical |
| HashMap linking | 15-25 | Medium | High |
| Closure semantics | 10-15 | Medium | Medium |
| Hasher trait linking | 10-15 | Low | Medium |
| Panic automation | 5-10 | Low | Low |
| **Total** | **80-125** | - | - |

### 6.2 Phased Approach

**Phase 1: Foundation (Week 1-2)**
- Complete SmallStep.step implementation
- Prove basic monad laws from step semantics
- Estimated: 20-30 hours

**Phase 2: HashMap (Week 3)**
- Define HashMap simulation correspondence
- Prove get/insert stepping lemmas
- Estimated: 15-25 hours

**Phase 3: Operations (Week 4-5)**
- Prove get_executes from stepping lemmas
- Prove insert_executes from stepping lemmas
- Delete follows from insert
- Estimated: 20-30 hours

**Phase 4: Polish (Week 6)**
- Trait resolution for Hasher
- Batch verification linking
- Panic analysis
- Estimated: 15-25 hours

---

## 7. Verification Confidence

### 7.1 What We Can Trust

| Category | Confidence | Reason |
|----------|------------|--------|
| Type linking | High | Direct structural correspondence |
| Simulation properties | High | Fully proven in tree.v |
| Composition theorems | High | Follow from simulation |
| Termination | High | Pure functions on finite data |

### 7.2 What Needs Verification

| Category | Current Confidence | Path to High |
|----------|-------------------|--------------|
| Execution axioms | Medium | M monad interpreter |
| Panic freedom | Medium | Code analysis + testing |
| Batch verification | Medium | Property-based testing |

### 7.3 Testing Coverage

| Test Type | Status | Details |
|-----------|--------|---------|
| QuickChick properties | ✅ 50,000 tests | 5 properties |
| OCaml extraction | ✅ 10/10 tests | FFI bridge |
| Rust integration | Partial | Manual testing |

---

## 8. Axiom Reduction Progress

### 8.1 Axioms Converted to Lemmas

| Former Axiom | New Status | Date |
|--------------|------------|------|
| `run_pure` | Laws.run_pure (proven) | Dec 2024 |
| `run_panic` | Laws.run_panic (proven) | Dec 2024 |

### 8.2 Axioms Pending Conversion

| Axiom | Blocked By | ETA |
|-------|------------|-----|
| `get_executes` | HashMap linking | Phase 3 |
| `insert_executes` | HashMap linking | Phase 3 |
| `delete_executes` | insert_executes | Phase 3 |
| `run_bind` | Step semantics | Phase 1 |
| `run_eval_sound` | Full interpreter | Phase 2 |

---

## 9. Action Items

### Immediate (This Week)

- [ ] Review SmallStep.step cases for completeness
- [ ] Document missing LowM constructors
- [ ] Set up test harness for step relation

### Short-term (This Month)

- [ ] Complete Phase 1 (M monad foundation)
- [ ] Begin HashMap correspondence proofs
- [ ] Add more QuickChick properties for edge cases

### Medium-term (This Quarter)

- [ ] Complete Phases 2-3 (execution proofs)
- [ ] Convert execution axioms to theorems
- [ ] Document any remaining axioms

### Long-term

- [ ] Complete Phase 4 (polish)
- [ ] Explore certified extraction
- [ ] Consider mechanized panic analysis

---

## 10. Key Design Decisions

### 10.1 Root Field Abstraction

The Rust `UnifiedBinaryTree` has a `root: Node` field that caches the Merkle root. The linking layer treats this specially:

**Design:**
- `SimTreeLink.φ` encodes the root as `Node::Empty` regardless of actual Rust value
- `tree_refines` only checks stems match (ignores root field)
- `sim_root_hash` computes root on-demand from stems

**Rationale:**
1. The stems map is the authoritative state (source of truth)
2. The root is deterministically derivable from stems
3. Rust caches for performance; simulation computes on-demand

**Connection Axiom:**
The `HashLink.root_hash_executes` axiom ties the two together:
```coq
Axiom root_hash_executes :
  forall (H : Ty.t) (sim_t : SimTree),
  forall (rust_tree : Value.t) (s : Run.State),
    tree_refines H rust_tree sim_t ->
    wf_tree sim_t ->
    exists (s' : Run.State),
      Run.run (rust_root_hash H [] [] [rust_tree]) s = 
      (Outcome.Success (φ (sim_root_hash sim_t)), s').
```

This states that for any trees where `tree_refines` holds, the Rust root hash computation produces the same result as the simulation's `sim_root_hash`.

**Locations:**
- `linking/types.v:SimTreeLink` - encoding with root=Empty
- `linking/operations.v:tree_refines` - refinement ignoring root
- `linking/operations.v:HashLink.root_hash_executes` - connection axiom

---

## 11. References

- [axiom_audit.md](axiom_audit.md) - Complete axiom listing
- [LINKING_LAYER_SETUP.md](LINKING_LAYER_SETUP.md) - Build instructions
- [SPEC_RUST_LINKAGE.md](SPEC_RUST_LINKAGE.md) - Operation mapping
- [RUST_MODEL_COMPARISON.md](RUST_MODEL_COMPARISON.md) - Rust↔Coq comparison
- `linking/interpreter.v` - M monad interpreter
- `linking/monad.v` - Step semantics
- `linking/operations.v` - Operation linking
- `linking/types.v` - Type linking

---

*Last updated: December 2024*
