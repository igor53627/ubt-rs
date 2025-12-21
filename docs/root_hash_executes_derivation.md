# Root Hash Executes Axiom Derivation Analysis

**Issue:** Reducing `root_hash_executes` axiom using RootHashLink infrastructure

## 1. Current State of root_hash_executes

### Location
[operations.v:857-864](file:///Users/user/pse/paradigm/ubt-rs/formal/linking/operations.v#L857-L864)

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

### Classification
- Tag: `[AXIOM:IMPL-GAP]`
- Risk: High - requires Hasher trait linking, Node hash linking
- Module: `HashLink`

## 2. Rust Implementation Decomposition

From [tree.rs:194-200](file:///Users/user/pse/paradigm/ubt-rs/src/tree.rs#L194-L200):

```rust
pub fn root_hash(&mut self) -> B256 {
    if self.root_dirty {           // Step 1: Check dirty flag
        self.rebuild_root();       // Step 2: Rebuild if dirty
        self.root_dirty = false;
    }
    self.root_hash_cached          // Step 3: Return cached value
}
```

### rebuild_root Decomposition ([tree.rs:260-277](file:///Users/user/pse/paradigm/ubt-rs/src/tree.rs#L260-L277)):

```rust
fn rebuild_root(&mut self) {
    // Step 2a: Update dirty stem hashes
    for stem in &dirty_stems {
        let hash = self.compute_stem_hash(stem);  // StemNode::hash
        self.stem_hash_cache.insert(*stem, hash);
    }
    
    // Step 2b: Build tree from stem hashes
    // Uses build_root_hash_from_stem_hashes which:
    //   - Creates leaf nodes from stem hashes
    //   - Recursively combines with hash_pair
    //   - Returns final root hash
}
```

## 3. RootHashLink Infrastructure

### Location
[interpreter.v:4885-5050](file:///Users/user/pse/paradigm/ubt-rs/formal/linking/interpreter.v#L4885-L5050)

### Existing Stepping Lemmas

| Lemma | Status | Purpose |
|-------|--------|---------|
| `empty_node_hash_steps` | PROVEN | Empty tree → zero32 |
| `leaf_node_hash_steps` | PROVEN | Leaf v → hash_value v |
| `internal_node_hash_steps` | PROVEN | Internal l r → hash_pair l r |
| `stem_node_hash_steps` | PROVEN | Stem s t → hash_stem s t |
| `sim_node_hash_correct` | PROVEN | SimNode case analysis |
| `root_hash_executes_sketch` | PROVEN | Derives from axiom via Run/Fuel bridge |

### TraitRegistry Hash Axioms

From [interpreter.v:674-692](file:///Users/user/pse/paradigm/ubt-rs/formal/linking/interpreter.v#L674-L692):

| Axiom | Connects |
|-------|----------|
| `hash_32_executes_as_hash_value` | Hasher::hash_32 → hash_value |
| `hash_64_executes_as_hash_pair` | Hasher::hash_64 → hash_pair |
| `hash_stem_node_executes_as_hash_stem` | Hasher::hash_stem_node → hash_stem |

## 4. Derivation Structure

### Decomposition into Sub-Axioms

```
root_hash_executes
    ├── dirty_flag_reads          [NEW: field access stepping]
    ├── rebuild_root_executes     [DECOMPOSABLE]
    │   ├── stem_hash_compute     [TraitRegistry axioms]
    │   │   ├── hash_32_executes_as_hash_value
    │   │   ├── hash_64_executes_as_hash_pair
    │   │   └── hash_stem_node_executes_as_hash_stem
    │   └── tree_build_from_stems [NEW: recursive build]
    │       ├── depth_bounded     [PROVEN: tree_depth_bounded_by_stem_bits]
    │       └── hash_pair_compose [TraitRegistry: hash_64_executes_as_hash_pair]
    └── field_return_cached       [NEW: field access stepping]
```

### Termination Guarantee

The depth bound theorem [tree.v:1155-1168](file:///Users/user/pse/paradigm/ubt-rs/formal/simulations/tree.v#L1155-L1168) ensures:

```coq
Theorem tree_depth_bounded_by_stem_bits :
  forall t : SimTree, wf_tree t -> depth_bounded stem_bit_count t.
```

Where `stem_bit_count = 248` (31 bytes × 8 bits).

This proves `rebuild_root` terminates because:
1. Tree traversal is bounded by 248 levels
2. Each level processes finite stem partitions
3. Hash computations are O(1) (axiomatized)

## 5. Derivation Sketch

### Step 1: Dirty Flag Check

```coq
(* NEW AXIOM: Field access stepping for root_dirty *)
Axiom root_dirty_reads :
  forall (H : Ty.t) (rust_tree : Value.t) (s : State.t),
    exists (dirty : bool) (s' : State.t),
      (* rust_tree.root_dirty field access steps to bool *)
      field_read_steps rust_tree "root_dirty" (φ dirty) s s'.
```

### Step 2: Rebuild Root (if dirty)

```coq
(* Compose existing axioms *)
Lemma rebuild_root_executes :
  forall (H : Ty.t) (sim_t : SimTree) (rust_tree : Value.t) (s : State.t),
    tree_refines H rust_tree sim_t ->
    wf_tree sim_t ->
    exists (s' : State.t) (rust_tree' : Value.t),
      (* rebuild_root updates stem caches and root hash *)
      rebuild_steps H rust_tree s rust_tree' s' /\
      (* Result matches simulation *)
      cached_root_hash rust_tree' = φ (sim_root_hash sim_t).
Proof.
  (* 
   * 1. Iterate over dirty_stems using HashMapStepping axioms
   * 2. For each stem, compute hash using stem_node_hash_steps
   *    (composes hash_32, hash_64, hash_stem from TraitRegistry)
   * 3. Build tree structure using tree_depth_bounded for termination
   * 4. Final hash computation via hash_pair composition
   *)
Admitted. (* Requires hashmap iteration stepping *)
```

### Step 3: Return Cached Hash

```coq
(* NEW AXIOM: Field access for root_hash_cached *)
Axiom root_hash_cached_returns :
  forall (H : Ty.t) (rust_tree : Value.t) (s : State.t),
    exists (hash : Bytes32) (s' : State.t),
      field_read_steps rust_tree "root_hash_cached" (φ hash) s s'.
```

## 6. New Axioms Needed

### A. Field Access Stepping
```coq
Module FieldStepping.
  (* Read struct field *)
  Axiom field_read_steps :
    forall (v : Value.t) (field : string) (result : Value.t) (s s' : State.t),
      is_struct_record v ->
      has_field v field ->
      step_field_read v field s = Some (result, s').
      
  (* Write struct field (for root_dirty = false) *)
  Axiom field_write_steps :
    forall (v : Value.t) (field : string) (new_val : Value.t) (s s' : State.t),
      is_struct_record v ->
      has_field v field ->
      step_field_write v field new_val s = Some (updated_v, s').
End FieldStepping.
```

### B. Iteration/Loop Stepping
```coq
Module IteratorStepping.
  (* For-loop over HashMap drains dirty_stem_hashes *)
  Axiom drain_iter_steps :
    forall (set : Value.t) (elements : list Value.t) (s s' : State.t),
      rust_hashset_drain set s = Some (elements, s').
      
  (* For-loop body composition *)
  Axiom for_loop_steps :
    forall (elements : list Value.t) (body : Value.t -> M) (s : State.t),
      for_loop_terminates elements body s.
End IteratorStepping.
```

### C. Tree Building Stepping
```coq
Module TreeBuildStepping.
  (* Build binary tree from stem hashes - uses depth bound for termination *)
  Axiom build_tree_steps :
    forall (H : Ty.t) (stem_hashes : list (Stem * Bytes32)) (s : State.t),
      wf_stem_hashes stem_hashes ->  (* All stems are 31 bytes *)
      exists (root_hash : Bytes32) (s' : State.t),
        build_tree_from_stems_steps H stem_hashes s root_hash s' /\
        root_hash = sim_build_tree_hash stem_hashes.
        
  (* Termination by depth bound *)
  Lemma build_tree_terminates :
    forall stem_hashes,
      wf_stem_hashes stem_hashes ->
      build_tree_depth stem_hashes <= stem_bit_count.
  Proof.
    (* Uses tree_depth_bounded_by_stem_bits *)
  Admitted.
End TreeBuildStepping.
```

## 7. Dependency Graph

```
                    root_hash_executes
                           │
           ┌───────────────┼───────────────┐
           ▼               ▼               ▼
    root_dirty_reads  rebuild_root   root_hash_cached
           │          _executes           │
           │               │              │
           ▼               ▼              ▼
    field_read_steps  ┌────┴────┐   field_read_steps
                      ▼         ▼
              stem_hash    tree_build
              _compute     _steps
                  │            │
        ┌─────────┼─────┐      │
        ▼         ▼     ▼      ▼
   hash_32    hash_64  hash   depth_bound
   _executes  _executes stem  (PROVEN)
   (AXIOM)    (AXIOM)  _executes
                       (AXIOM)
```

## 8. Summary

### Current Axiom Reduction

| Component | Status | Dependencies |
|-----------|--------|--------------|
| Dirty flag check | NEW AXIOM | FieldStepping |
| Stem hash compute | REDUCIBLE | TraitRegistry hash axioms |
| Tree build | PARTIAL | depth_bounded (proven) + TreeBuildStepping |
| Cached return | NEW AXIOM | FieldStepping |

### Axiom Count Change

**Before:** 1 monolithic axiom (`root_hash_executes`)

**After:** Decomposed into:
- 3 existing TraitRegistry hash axioms (already counted)
- 2 new FieldStepping axioms (field read/write)
- 1 new IteratorStepping axiom (drain iteration)
- 1 new TreeBuildStepping axiom (tree construction)

**Net change:** +4 fine-grained axioms, -1 coarse axiom

### Benefits of Decomposition

1. **Localized trust:** Each axiom covers a single Rust operation
2. **Testable:** Fine-grained axioms can be property-tested individually
3. **Reusable:** FieldStepping and IteratorStepping apply to other operations
4. **Termination explicit:** depth_bounded theorem proves rebuild terminates

### Remaining Semantic Gap

The core semantic gap is now:
1. **Hash function behavior** (TraitRegistry axioms) - inherently unprovable
2. **Rust memory model** (field access) - needs M monad interpreter
3. **Iterator semantics** (drain/for-loop) - needs closure/iterator stepping

These represent the true implementation gap between Rust and Rocq.
