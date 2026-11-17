# Specification-to-Rust Linkage Documentation

This document explains how the Coq (Rocq) formal specifications connect to the Rust implementation of the Unified Binary Tree (UBT).

## Overview

The verification follows a **refinement approach**:

```text
┌─────────────────────────────────────────────────────────────────┐
│  specs/tree_spec.v         Abstract specification (EIP-7864)   │
│       ↓ refines                                                 │
│  simulations/tree.v        Pure functional simulation           │
│       ↓ linked via φ                                            │
│  linking/types.v           Type correspondence                  │
│  linking/operations.v      Behavioral equivalence               │
│       ↓ translation via rocq-of-rust                            │
│  src/tree.v                Translated Rust (monadic)            │
│       ↓                                                         │
│  Rust ubt crate            Deployed implementation              │
└─────────────────────────────────────────────────────────────────┘
```

## Module Correspondence

### Coq Module → Rust Module Mapping

| Coq Module | Rust Module | Purpose |
|------------|-------------|---------|
| `specs/tree_spec.v` | — | Abstract specification (no Rust equivalent) |
| `specs/embedding_spec.v` | `src/embedding.rs` | EIP-7864 key derivation |
| `simulations/tree.v` | `src/tree/` | Tree data structure and operations |
| `simulations/crypto.v` | `src/hash.rs` | Hash function abstraction |
| `simulations/verkle.v` | — | Verkle proof support (future) |
| `linking/types.v` | — | Type linking (φ encoding) |
| `linking/operations.v` | — | Behavioral equivalence proofs |
| `src/tree.v` | `src/tree/` (translated when it was the single file `src/tree.rs`) | Auto-translated Rust code |
| `src/node.v` | `src/node.rs` | Node types |
| `src/key.v` | `src/key.rs` | Key types (Stem, TreeKey) |

---

## SimTree ↔ Rust UnifiedBinaryTree Correspondence

### Type Structure

**Coq SimTree** (simulations/tree.v:532-534):
```coq
Record SimTree := mkSimTree {
  st_stems : StemMap
}.
```

**Rust UnifiedBinaryTree** (src/tree/mod.rs, cache fields omitted):
```rust
pub struct UnifiedBinaryTree<H: Hasher = Blake3Hasher, S: NodeStore = InMemoryStore> {
    hasher: H,
    store: S,
    // ... dirty flags and hash caches
}
```

### φ Encoding (linking/types.v, module `SimTreeLink` at line 615)

The `SimTreeLink` module defines how Coq `SimTree` values encode to Rust `Value.t`:

```coq
Module SimTreeLink.
  Definition Rust_ty (H : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "ubt::tree::UnifiedBinaryTree") [] [H].
  
  Global Instance IsLink (H : Ty.t) : Link SimTree := {
    Φ := Rust_ty H;
    φ t := Value.StructRecord "ubt::tree::UnifiedBinaryTree" [] [H]
             [("root", Value.StructTuple "ubt::node::Node::Empty" [] [] []);
              ("hasher", Value.StructTuple "unit" [] [] []);
              ("stems", φ (st_stems t))];
  }.
End SimTreeLink.
```

**Note:** This encoding models the translated structure in `formal/src/`, which predates crate version 0.5.0. That structure has one type parameter and the fields `root`, `hasher` and `stems`. The encoding does not cover the current `UnifiedBinaryTree<H, S>` shown above, which has a `store: S` field and no `root` field.

### Refinement Relation (linking/operations.v:171-172)

```coq
Definition tree_refines (H : Ty.t) (rust_tree : Value.t) (sim_tree : SimTree) : Prop :=
  rust_tree = @φ SimTree (SimTreeLink.IsLink H) sim_tree.
```

This states that a Rust tree value `rust_tree` **refines** a simulation tree `sim_tree` when the Rust value is exactly the φ-encoding of the simulation tree.

---

## Operation Mapping

### sim_tree_get ↔ tree.get()

| Aspect | Coq | Rust |
|--------|-----|------|
| Definition | `simulations/tree.v:539-543` | `src/tree/mod.rs::get()` |
| Linking | `linking/operations.v:372` | — |
| Verification | Axiom `get_executes` | — |

**Coq Definition:**
```coq
Definition sim_tree_get (t : SimTree) (k : TreeKey) : option Value :=
  match stems_get (st_stems t) (tk_stem k) with
  | Some submap => sim_get submap (tk_subindex k)
  | None => None
  end.
```

**Rust Definition (translated to Coq in src/tree.v):**
```coq
Definition rust_get (H : Ty.t) := src.tree.tree.Impl_ubt_tree_UnifiedBinaryTree_H.get H.
```

**Linking Axiom** (operations.v:339-347):
```coq
Axiom get_executes :
  forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
  forall (rust_tree : Value.t) (s : Run.State),
    tree_refines H rust_tree sim_t ->
    UBT.Sim.tree.wf_tree sim_t ->
    wf_stem (tk_stem k) ->
    exists (s' : Run.State),
      Run.run (rust_get H [] [] [rust_tree; φ k]) s = 
      (Outcome.Success (φ (sim_tree_get sim_t k)), s').
```

---

### sim_tree_insert ↔ tree.insert()

| Aspect | Coq | Rust |
|--------|-----|------|
| Definition | `simulations/tree.v:546-555` | `src/tree/mod.rs::insert()` |
| Linking | `linking/operations.v:488` | — |
| Verification | Axiom `insert_executes` | — |

**Coq Definition:**
```coq
Definition sim_tree_insert (t : SimTree) (k : TreeKey) (v : Value) : SimTree :=
  let stem := tk_stem k in
  let idx := tk_subindex k in
  let old_submap := 
    match stems_get (st_stems t) stem with
    | Some m => m
    | None => []
    end in
  let new_submap := sim_set old_submap idx v in
  mkSimTree (stems_set (st_stems t) stem new_submap).
```

**Linking Axiom** (operations.v:404-414):
```coq
Axiom insert_executes :
  forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
  forall (rust_tree : Value.t) (s : Run.State),
    tree_refines H rust_tree sim_t ->
    UBT.Sim.tree.wf_tree sim_t ->
    wf_stem (tk_stem k) ->
    wf_value v ->
    exists (rust_tree' : Value.t) (s' : Run.State),
      Run.run (rust_insert H [] [] [rust_tree; φ k; φ v]) s =
      (Outcome.Success rust_tree', s') /\
      tree_refines H rust_tree' (sim_tree_insert sim_t k v).
```

---

### sim_tree_delete ↔ tree.delete()

| Aspect | Coq | Rust |
|--------|-----|------|
| Definition | `simulations/tree.v:558-559` | `src/tree/mod.rs::delete()` |
| Linking | `linking/operations.v:635-650` | — |
| Verification | Theorem `delete_executes`, proven for the model term `rust_delete` by applying the axiom `insert_executes` | — |

**Coq Definition:**
```coq
Definition sim_tree_delete (t : SimTree) (k : TreeKey) : SimTree :=
  sim_tree_insert t k zero32.
```

In the Coq model, delete is defined as insert with the zero value. The linking layer also defines `rust_delete` as `rust_insert` with `zero32` (`linking/operations.v:573-574`); it does not use a translation of the Rust `delete()` method. The Rust `delete()` is a separate method: it removes the value (`set_value` with `B256::ZERO`) only when the stem exists, and it removes the stem node when no values are left.

**Linking Theorem** (operations.v:611-618):
```coq
Theorem delete_is_insert_zero :
  forall (t : SimTree) (k : TreeKey),
    sim_tree_delete t k = sim_tree_insert t k zero32.
```

---

### sim_root_hash ↔ tree.root_hash()

| Aspect | Coq | Rust |
|--------|-----|------|
| Definition | `simulations/tree.v:1001-1003` (folds `stem_entry_hash` over `st_stems`; `stem_entry_hash` uses `subindex_map_hash`) | `src/tree/hash.rs::root_hash()` |
| Linking | `linking/operations.v:779-785` | — |
| Verification | Axiom `root_hash_executes` | — |

The root hash computation uses the abstract hash functions defined in `simulations/crypto.v` (`simulations/tree.v:993-1003`):

```coq
Definition subindex_map_hash (m : SubIndexMap) : Bytes32 :=
  fold_left (fun acc p => hash_pair acc (hash_value (snd p))) m zero32.

Definition stem_entry_hash (s : Stem) (m : SubIndexMap) : Bytes32 :=
  hash_stem s (subindex_map_hash m).

Definition sim_root_hash (t : SimTree) : Bytes32 :=
  fold_left (fun acc p => hash_pair acc (stem_entry_hash (fst p) (snd p)))
            (st_stems t) zero32.
```

`sim_root_hash` does not call `sim_node_hash` (`simulations/tree.v:372-379`), whose `SimStem` branch ignores the stored values.

---

## Complete Mapping Table

| Coq Definition | Rust Function | Verified? | Axiom/Proof | Notes |
|----------------|---------------|-----------|-------------|-------|
| `empty_tree` | `UnifiedBinaryTree::new()` | **Proven** | `NewLink.new_refines` | Empty tree creation |
| `sim_tree_get` | `tree.get()` | **Axiom** | `GetLink.get_executes` | Requires monadic semantics |
| `sim_tree_insert` | `tree.insert()` | **Axiom** | `InsertLink.insert_executes` | Requires HashMap linking |
| `sim_tree_delete` | `tree.delete()` | **Conditional** | `DeleteLink.delete_executes` (theorem; applies axiom `InsertLink.insert_executes`) | Proven for `rust_delete`, defined as `rust_insert` with `zero32`; no link to the Rust `delete()` method |
| `sim_root_hash` | `tree.root_hash().unwrap()` | **Axiom** | `HashLink.root_hash_executes` | Requires hash linking |
| `wf_tree` | — | **Proven** | `insert_preserves_wf` | Well-formedness invariant |
| `get_empty` | — | **Proven** | Direct | Empty returns None |
| `get_insert_same` | — | **Proven** | Direct | Insert-get correctness |
| `get_insert_other_stem` | — | **Proven** | Direct | Non-interference |
| `get_insert_other_subindex` | — | **Proven** | Direct | Non-interference |
| `get_delete` | — | **Proven** | Direct | Delete correctness |
| `insert_order_independent_stems` | — | **Proven** | Direct | Closed with `Qed` in `simulations/tree.v` |
| `hash_value` | `Hasher::hash_32()` | **Axiom** | Abstract parameter | Crypto abstraction |
| `hash_pair` | `Hasher::hash_64()` | **Axiom** | Abstract parameter | Crypto abstraction |
| `hash_stem` | `Hasher::hash_stem_node()` | **Axiom** | Abstract parameter | Crypto abstraction |
| `verify_inclusion_proof` | `proof.verify()` | **Axiom** | `verify_executes` | Merkle proof verification |
| `verify_batch_inclusion` | `batch_verify()` | **Axiom** | `rust_verify_batch_inclusion_executes` | Batch proof verification |
| `InclusionProof` | `InclusionProof` | Stub | — | Proof structure (axiomatized) |
| `ExclusionProof` | `ExclusionProof` | Stub | — | Proof structure (axiomatized) |
| `BatchInclusionProof` | `Vec<InclusionProof>` | Stub | — | Batch proof type |
| `exclusion_proof_soundness` | — | **Axiom** | — | Connects proofs to tree semantics |

---

## Type Linking Table

| Coq Type | Rust Type | Link Module | φ Encoding |
|----------|-----------|-------------|------------|
| `Byte` | `u8` | `ByteLink` | `Value.Integer IntegerKind.U8` |
| `Bytes32` | `alloy_primitives::FixedBytes<32>` | `Bytes32Link` | `Value.StructTuple` with array |
| `Bytes31` | `[u8]` | `Bytes31Link` | `Value.Array` |
| `Stem` | `ubt::key::Stem` | `StemLink` | `Value.StructTuple` |
| `SubIndex` | `u8` | `SubIndexLink` | `Value.Integer IntegerKind.U8` |
| `TreeKey` | `ubt::key::TreeKey` | `TreeKeyLink` | `Value.StructRecord` |
| `Value` | `B256` | `ValueLink` | Same as `Bytes32Link` |
| `option A` | `Option<A>` | `OptionLink` | `Option::None` / `Option::Some` |
| `SubIndexMap` | `HashMap<u8, B256>` | `SubIndexMapLink` | HashMap struct |
| `StemMap` | `HashMap<Stem, StemNode>` | `StemMapLink` | HashMap struct |
| `SimTree` | `UnifiedBinaryTree<H>` | `SimTreeLink` | Full struct encoding |

---

## Trust Boundaries

### What Must Be Trusted

1. **Rust Compiler & Runtime**
   - Correct compilation of Rust to machine code
   - Memory safety guarantees
   - HashMap implementation correctness

2. **Hash Function Implementations**
   - `Blake3Hasher`, `Sha256Hasher` behave as specified
   - Collision resistance holds for the hash function
   - Zero values hash to zero (EIP-7864 requirement)

3. **rocq-of-rust Translation**
   - Semantic preservation from Rust to Coq
   - Correct monadic encoding of side effects
   - Accurate type translation

4. **RocqOfRust Library**
   - M monad correctly models Rust execution
   - Value.t correctly represents Rust values
   - Trait resolution is sound

5. **External Dependencies**
   - `alloy-primitives` crate correctness
   - `std::collections::HashMap` correctness

### What Is Verified (Simulation Level)

1. **Tree Semantics** (fully proven):
   - Get from empty returns None
   - Insert then get returns inserted value
   - Insert doesn't affect other keys
   - Delete removes value
   - Operations preserve well-formedness

2. **Co-location** (fully proven):
   - Same stem → shared storage (EIP-7864)
   - Account data fields share stem
   - Code chunks grouped correctly

3. **Merkle Proof Soundness** (proven):
   - Valid inclusion proof → value is in tree
   - Same witness path → same value (collision resistance)

### What Is Axiomatized

1. **Execution Axioms** (`*_executes`):
   - Monadic Rust code terminates with expected result
   - Requires full M monad interpreter (not yet developed)

2. **Panic Freedom**:
   - Well-formed inputs never trigger `panic!`
   - Requires control flow analysis

3. **Cryptographic Properties**:
   - Collision resistance (standard assumption)
   - Determinism (derivable but stated explicitly)
   - Zero-hash behavior (design choice)

### What Is Tested (QuickChick)

- Property-based testing of simulation operations
- Randomized tree construction and queries
- Shrinking for counterexample minimization
- See `proofs/quickchick_tests.v` for test definitions

---

## How to Verify the Linkage

### 1. Build Everything
```bash
eval $(opam env --switch=rocq-9) && make clean && make all && make linking
```

### 2. Check Axiom Count
```bash
grep -c "Axiom\|Admitted" linking/operations.v
```

### 3. Inspect Key Theorems
```bash
coqc -Q simulations UBT.Sim -R ~/pse/paradigm/rocq-of-rust/RocqOfRust RocqOfRust \
  -Q src src -Q linking UBT.Linking linking/operations.v 2>&1 | grep -i "error\|warning"
```

### 4. Review Refinement Proofs
The key files to review:
- `linking/types.v` — Type correspondence
- `linking/operations.v` — Behavioral equivalence
- `simulations/tree.v` — Core properties (proven)

---

## Future Work

1. **Develop M Monad Interpreter**: Full step semantics for `Run.run`
2. **Prove Execution Axioms**: Replace `get_executes`, `insert_executes`, etc.
3. **Link HashMap Operations**: Connect Rust HashMap to Coq StemMap
4. **Verify Panic Freedom**: Prove all `panic!` calls unreachable
5. **Certified Extraction**: Extract Coq simulation to verified OCaml/Rust
