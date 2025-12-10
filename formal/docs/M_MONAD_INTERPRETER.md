# M Monad Interpreter Design Document

**Issue:** #24 - Develop M monad interpreter for full linking proofs  
**Date:** December 2024  
**Status:** Design Phase  
**Related Files:**  
- `formal/linking/operations.v` - Current axioms  
- `formal/linking/interpreter.v` - Interpreter skeleton  
- `formal/linking/types.v` - Type linking definitions

---

## Executive Summary

The linking layer in `operations.v` uses **14 axioms** for monadic execution semantics. A full M monad interpreter would convert these to proven theorems, strengthening the overall verification. This document specifies the interpreter design, proof strategies, and implementation roadmap.

### Current Axiom Status

| Category | Count | Examples |
|----------|-------|----------|
| Monad Laws | 3 | `run_pure`, `run_bind`, `run_panic` |
| Operation Execution | 5 | `get_executes`, `insert_executes`, `delete_executes`, `new_executes`, `root_hash_executes` |
| Panic Freedom | 4 | `get_no_panic`, `insert_no_panic`, etc. |
| Batch Verification | 2 | `rust_verify_batch_inclusion_executes`, `rust_verify_shared_executes` |

---

## 1. Current State of M Monad Axioms

### 1.1 Monad Law Axioms (`operations.v:205-226`)

```coq
(* Already provable with step semantics *)
Axiom run_pure : forall (v : Value.t) (s : State),
  run (M.pure v) s = (Outcome.Success v, s).

Axiom run_bind : forall (m : M) (f : Value.t -> M) (s : State),
  run (M.let_ m f) s = 
  match run m s with
  | (Outcome.Success v, s') => run (f v) s'
  | (Outcome.Panic e, s') => (Outcome.Panic e, s')
  | (Outcome.Diverge, s') => (Outcome.Diverge, s')
  end.

Axiom run_panic : forall (msg : string) (s : State),
  run (M.panic (Panic.Make msg)) s = (Outcome.Panic (existS string msg), s).
```

**Status:** These are standard monad laws. `interpreter.v` already has `Laws.run_pure` and `Laws.run_panic` proven. `run_bind` needs compositional proof via `Laws.let_sequence`.

### 1.2 Operation Execution Axioms (`operations.v:349-495`)

```coq
Axiom get_executes :
  forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
  forall (rust_tree : Value.t) (s : Run.State),
    tree_refines H rust_tree sim_t ->
    wf_tree sim_t ->
    wf_stem (tk_stem k) ->
    exists (s' : Run.State),
      Run.run (rust_get H [] [] [rust_tree; φ k]) s = 
      (Outcome.Success (φ (sim_tree_get sim_t k)), s').
```

**Status:** Requires full interpreter with HashMap operation semantics.

### 1.3 Panic Freedom Axioms (implied by execution axioms)

These claim operations don't panic on well-formed inputs. They follow from the execution axioms producing `Success` outcomes.

---

## 2. Required Components for Full Interpreter

### 2.1 Core Execution Engine

| Component | Description | Status |
|-----------|-------------|--------|
| `SmallStep.step` | Single-step evaluation | Skeleton in `interpreter.v` |
| `Config.t` | Evaluation configuration (term + state) | Defined in `operations.v:126` |
| `ExecState.t` | Heap memory model | Defined in `operations.v:86-113` |
| `Fuel.run` | Bounded evaluation | Referenced, needs implementation |

### 2.2 Primitive Operations

The M monad uses `LowM.CallPrimitive` for state operations:

| Primitive | Semantics |
|-----------|-----------|
| `StateAlloc v` | Allocate `v` on heap, return pointer |
| `StateRead ptr` | Read value at heap address |
| `StateWrite ptr v` | Write `v` to heap address |
| `GetFunction name` | Resolve function by name |
| `GetAssociatedFunction ty name` | Resolve impl method |
| `GetTraitMethod trait ty method` | Resolve trait method |

### 2.3 Trait Resolution

RocqOfRust encodes trait method calls as `GetTraitMethod` primitives:

```coq
LowM.CallPrimitive 
  (Primitive.GetTraitMethod "ubt::hasher::Hasher" H "hash_pair")
  (fun hash_pair_fn => ...)
```

**Required:** `TraitRegistry` mapping (trait, impl_type, method_name) → M body.

### 2.4 HashMap Operation Linking

The critical gap is connecting Rust HashMap operations to simulation maps:

| Rust Operation | Simulation Equivalent |
|----------------|----------------------|
| `HashMap::get(&key)` | `sim_stem_map_get m key` |
| `HashMap::entry(key).or_insert_with(f)` | `sim_stem_map_insert_or_get` |
| `HashMap::insert(key, value)` | `sim_stem_map_insert` |
| `SubIndexMap::get(&idx)` | `sim_subindex_map_get` |
| `SubIndexMap::insert(idx, v)` | `sim_subindex_map_insert` |

---

## 3. Step-by-Step Evaluation Semantics

### 3.1 LowM Constructors

```coq
Inductive LowM : Set :=
| Pure : Value.t + Exception.t -> LowM
| Let : LowM -> (Value.t + Exception.t -> LowM) -> LowM
| CallPrimitive : Primitive.t -> (Value.t -> LowM) -> LowM
| CallClosure : Value.t -> list Value.t -> (Value.t + Exception.t -> LowM) -> LowM
| Loop : LowM -> LowM
| Impossible : string -> LowM.
```

### 3.2 Step Relation

```coq
Inductive StepResult : Set :=
| Step : Config.t -> StepResult        (* Normal step *)
| Terminal : Value.t -> StepResult     (* Pure value reached *)
| Exception : Exception.t -> StepResult (* Exception raised *)
| StuckState : StepResult.             (* Invalid state *)

Definition step (c : Config.t) : StepResult :=
  match Config.term c with
  | LowM.Pure (inl v) => Terminal v
  | LowM.Pure (inr exn) => Exception exn
  | LowM.Let e k => step_let e k (Config.state c)
  | LowM.CallPrimitive prim k => step_primitive prim k (Config.state c)
  | LowM.CallClosure closure args k => step_closure closure args k (Config.state c)
  | LowM.Loop body => step_loop body (Config.state c)
  | LowM.Impossible msg => StuckState
  end.
```

### 3.3 Let (Bind) Stepping

```coq
Definition step_let (e : LowM) (k : Value.t + Exception.t -> LowM) (s : State.t) : StepResult :=
  match e with
  | LowM.Pure (inl v) => 
      (* Value ready: apply continuation *)
      Step (Config.mk (k (inl v)) s)
  | LowM.Pure (inr exn) => 
      (* Exception: propagate through continuation *)
      Step (Config.mk (k (inr exn)) s)
  | _ => 
      (* Subterm needs stepping *)
      match step (Config.mk e s) with
      | Step c' => Step (Config.mk (LowM.Let (Config.term c') k) (Config.state c'))
      | Terminal v => Step (Config.mk (k (inl v)) s)
      | Exception exn => Step (Config.mk (k (inr exn)) s)
      | StuckState => StuckState
      end
  end.
```

### 3.4 Primitive Stepping

```coq
Definition step_primitive (prim : Primitive.t) (k : Value.t -> LowM) (s : State.t) : StepResult :=
  match prim with
  | Primitive.StateAlloc v =>
      let (s', addr) := ExecState.alloc s v in
      Step (Config.mk (k (Value.Pointer addr)) s')
      
  | Primitive.StateRead ptr =>
      match ExecState.read s ptr with
      | Some v => Step (Config.mk (k v) s)
      | None => StuckState  (* Invalid pointer *)
      end
      
  | Primitive.StateWrite ptr v =>
      let s' := ExecState.write s ptr v in
      Step (Config.mk (k Value.unit) s')
      
  | Primitive.GetTraitMethod trait impl_ty method =>
      match TraitRegistry.resolve_method trait impl_ty method with
      | Some body => Step (Config.mk (k (Value.Closure body)) s)
      | None => StuckState  (* Trait not registered *)
      end
      
  | _ => StuckState  (* Unimplemented primitive *)
  end.
```

---

## 4. HashMap Operations to Simulation Maps

### 4.1 Encoding Strategy

The Rust HashMap is encoded as a `Value.t` containing the map structure. The linking connects this to simulation types via `φ`:

```coq
(* types.v:183-190 *)
Global Instance IsLink : Link StemMap := {
  Φ := Rust_ty;
  φ m := Value.StructRecord "std::collections::hash::map::HashMap" []
           [StemLink.Rust_ty; Ty.path "ubt::node::StemNode"; 
            Ty.path "std::hash::random::RandomState"]
           [];
}.
```

### 4.2 HashMap.get Stepping

```coq
(* When stepping HashMap::get(&self, key) *)
Definition step_hashmap_get (map_val : Value.t) (key_val : Value.t) 
    (k : Value.t -> LowM) (s : State.t) : StepResult :=
  (* Decode map_val to StemMap, key_val to Stem *)
  let sim_map := decode_stem_map map_val in
  let sim_key := decode_stem key_val in
  let result := sim_stem_map_get sim_map sim_key in
  Step (Config.mk (k (φ result)) s).
```

### 4.3 Refinement Invariant

The key invariant maintained during stepping:

```coq
Definition map_refines (rust_map : Value.t) (sim_map : StemMap) : Prop :=
  rust_map = φ sim_map.
```

For each HashMap operation step, we must prove:
1. The step produces the correct result value
2. If state-modifying, the new map refines the updated simulation map

---

## 5. Proof Strategy for Each `*_executes` Axiom

### 5.1 `get_executes`

**Goal:** `rust_get` returns `φ (sim_tree_get sim_t k)`

**Strategy:**
1. Unfold `rust_get` to its M monad representation
2. The definition is roughly:
   ```rust
   pub fn get(&self, key: TreeKey) -> Option<Value> {
       self.stems.get(&key.stem)?.get_value(key.subindex)
   }
   ```
3. Step through `HashMap::get` call → produces `Option<StemNode>`
4. Case split on result:
   - `None`: return `None` (matches `sim_tree_get` when stem not found)
   - `Some(node)`: step through `StemNode::get_value`
5. Step through `SubIndexMap::get` inside StemNode → produces final `Option<Value>`

**Key Lemmas Needed:**
```coq
Lemma hashmap_get_refines :
  forall (m : StemMap) (key : Stem) (rust_map : Value.t) (s : State.t),
    map_refines rust_map m ->
    exists fuel s',
      Fuel.run fuel (Config.mk (hashmap_get_term rust_map (φ key)) s) =
      (Outcome.Success (φ (sim_stem_map_get m key)), s').

Lemma subindexmap_get_refines :
  forall (m : SubIndexMap) (idx : SubIndex) (rust_map : Value.t) (s : State.t),
    (* Similar structure *)
```

### 5.2 `insert_executes`

**Goal:** `rust_insert` returns tree refining `sim_tree_insert sim_t k v`

**Strategy:**
1. Unfold `rust_insert`:
   ```rust
   pub fn insert(&mut self, key: TreeKey, value: Value) {
       let node = self.stems.entry(key.stem).or_insert_with(StemNode::new);
       node.set_value(key.subindex, value);
       self.rebuild_root();
   }
   ```
2. Step through `HashMap::entry().or_insert_with()`:
   - If stem exists: get mutable reference
   - If new: create StemNode and insert
3. Step through `StemNode::set_value` → updates SubIndexMap
4. Step through `rebuild_root` → updates root hash (state modification)

**Key Challenge:** State threading through mutable operations

**Key Lemmas Needed:**
```coq
Lemma hashmap_entry_or_insert_refines :
  forall (m : StemMap) (key : Stem) (default : StemNode),
    (* Returns (updated_map, node_ref) *)
    
Lemma stemnode_set_value_refines :
  forall (node : StemNode) (idx : SubIndex) (v : Value),
    (* Updates SubIndexMap within node *)
```

### 5.3 `delete_executes`

**Goal:** `rust_delete` ≡ `rust_insert` with `zero32`

**Strategy:**
Delete is defined as insert with zero value:
```coq
Definition rust_delete (H : Ty.t) (tree : Value.t) (key : Value.t) : M :=
  InsertLink.rust_insert H [] [] [tree; key; φ zero32].
```

Proof reduces directly to `insert_executes` with `v = zero32`.

### 5.4 `root_hash_executes`

**Goal:** `rust_root_hash` returns `φ (sim_root_hash sim_t)`

**Strategy:**
1. Unfold root_hash computation (Merkle tree traversal)
2. Step through hash computations using `Hasher` trait methods
3. Use `TraitRegistry` to resolve `hash_pair`, `hash_stem_node` calls
4. Show computed hash equals simulation `sim_root_hash`

**Key Dependency:** Hasher trait registration

---

## 6. Implementation Roadmap

### Phase 1: Core Step Semantics (Week 1-2)

**Deliverables:**
- [ ] Complete `SmallStep.step` for `Pure`, `Let` constructors
- [ ] Implement `step_primitive` for `StateAlloc`, `StateRead`, `StateWrite`
- [ ] Prove monad laws (`run_pure`, `run_panic`) as theorems
- [ ] Implement `Fuel.run` bounded execution

**Success Criteria:** Can evaluate simple M monad terms to completion.

### Phase 2: Trait Resolution (Week 3)

**Deliverables:**
- [ ] Populate `TraitRegistry` with UBT trait implementations:
  - `Hasher` for `PoseidonHasher` and `Keccak256Hasher`
  - `Default` for `UnifiedBinaryTree`
  - `Hash` for primitive types used as HashMap keys
- [ ] Implement `step_primitive` for `GetTraitMethod`
- [ ] Test trait resolution with simple hasher calls

**Success Criteria:** Can resolve and call trait methods.

### Phase 3: HashMap Linking (Week 4-5)

**Deliverables:**
- [ ] Define `decode_stem_map`, `decode_subindex_map` functions
- [ ] Prove `hashmap_get_refines` lemma
- [ ] Prove `hashmap_entry_or_insert_refines` lemma
- [ ] Prove `subindexmap_get_refines`, `subindexmap_insert_refines`

**Success Criteria:** HashMap operations step to correct simulation results.

### Phase 4: Operation Proofs (Week 6-7)

**Deliverables:**
- [ ] Convert `get_executes` axiom to theorem
- [ ] Convert `insert_executes` axiom to theorem
- [ ] Convert `delete_executes` axiom to theorem (via insert)
- [ ] Convert `root_hash_executes` axiom to theorem

**Success Criteria:** Operation axioms eliminated.

### Phase 5: Batch Verification (Week 8)

**Deliverables:**
- [ ] Convert `rust_verify_batch_inclusion_executes` axiom
- [ ] Convert `rust_verify_shared_executes` axiom

**Success Criteria:** All 14 linking axioms converted to theorems.

---

## 7. Key Lemmas to Prove

### 7.1 Termination Lemmas

```coq
(* All operations terminate with sufficient fuel *)
Lemma get_terminates : forall H sim_t k rust_tree s,
  tree_refines H rust_tree sim_t ->
  wf_tree sim_t ->
  wf_stem (tk_stem k) ->
  exists fuel, Fuel.terminates fuel (Config.mk (rust_get H [] [] [rust_tree; φ k]) s).

Lemma insert_terminates : forall H sim_t k v rust_tree s,
  tree_refines H rust_tree sim_t ->
  wf_tree sim_t ->
  wf_stem (tk_stem k) ->
  wf_value v ->
  exists fuel, Fuel.terminates fuel (Config.mk (rust_insert H [] [] [rust_tree; φ k; φ v]) s).
```

### 7.2 Refinement Preservation

```coq
(* Operations preserve the refinement relation *)
Lemma insert_preserves_refinement : forall H sim_t k v rust_tree rust_tree' s s',
  tree_refines H rust_tree sim_t ->
  (* After stepping insert to completion *)
  tree_refines H rust_tree' (sim_tree_insert sim_t k v).
```

### 7.3 Step Determinism

```coq
Lemma step_deterministic : forall c c1 c2,
  SmallStep.step c = Step c1 ->
  SmallStep.step c = Step c2 ->
  c1 = c2.
```

---

## 8. Testing Strategy

### 8.1 Concrete Evaluation Tests

Before attempting proofs, test the interpreter on concrete examples:

```coq
(* Test: Pure value evaluates immediately *)
Example test_pure :
  Fuel.run 1 (Config.mk (M.pure (Value.Integer IntegerKind.U64 42)) State.empty) =
  (Outcome.Success (Value.Integer IntegerKind.U64 42), State.empty).

(* Test: Let binding sequences correctly *)
Example test_let :
  exists fuel,
    Fuel.run fuel (Config.mk 
      (M.let_ (M.pure (Value.Integer IntegerKind.U64 1))
              (fun v => M.pure v)) 
      State.empty) =
    (Outcome.Success (Value.Integer IntegerKind.U64 1), State.empty).
```

### 8.2 Property-Based Testing (via extraction)

Extract interpreter to OCaml and use QuickCheck-style testing:
- Generate random M monad terms
- Evaluate with Fuel.run
- Compare to expected semantics

---

## 9. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| RocqOfRust M monad structure changes | Low | High | Pin RocqOfRust version |
| HashMap encoding incompatibility | Medium | High | Start with HashMap linking early |
| Trait resolution complexity | Medium | Medium | Simplify to statically-known impls |
| Fuel bounds too large | Low | Low | Use coinductive big-step if needed |
| Closure semantics mismatch | Medium | Medium | Verify closure encoding format |

---

## 10. Dependencies

### External
- RocqOfRust library (`RocqOfRust.RocqOfRust`, `RocqOfRust.links.M`, `RocqOfRust.simulations.M`)
- Coq standard library (Lists, ZArith, Strings)

### Internal
- `formal/linking/types.v` - Type linking definitions
- `formal/simulations/tree.v` - Simulation operations
- `formal/simulations/crypto.v` - Hash function axioms

---

## Appendix A: Axiom Inventory

### To Be Proven (via interpreter)

1. `Run.run_pure` - **Proven** in `Laws.run_pure`
2. `Run.run_bind` - **Partial** via `Laws.let_sequence`
3. `Run.run_panic` - **Proven** in `Laws.run_panic`
4. `Run.run_eval_sound` - Needs `Fuel.sufficient_implies_eval`
5. `GetLink.get_executes` - Needs HashMap linking
6. `InsertLink.insert_executes` - Needs HashMap linking
7. `DeleteLink.delete_executes` - Reduces to insert
8. `NewLink.new_executes` - Needs constructor stepping
9. `HashLink.root_hash_executes` - Needs trait resolution
10. `PanicFreedom.get_no_panic` - Follows from get_executes
11. `PanicFreedom.insert_no_panic` - Follows from insert_executes
12. `PanicFreedom.delete_no_panic` - Follows from delete_executes
13. `PanicFreedom.root_hash_no_panic` - Follows from root_hash_executes
14. `BatchVerifyLink.rust_verify_batch_inclusion_executes` - Needs batch stepping
15. `BatchVerifyLink.rust_verify_shared_executes` - Needs shared witness stepping

### Will Remain Axioms (crypto)

- Hash function primitives (`hash_value`, `hash_pair`, `hash_stem`)
- Collision resistance assumptions
- Verkle commitment operations

---

*Last updated: December 2024*
