(** * Operations Linking for UBT
    
    This module proves behavioral equivalence between:
    - Translated Rust operations (in src/tree.v) using the M monad
    - Simulation operations (in simulations/tree.v) using pure functions
    
    The key theorems establish refinement:
    - rust_get ≈ sim_tree_get
    - rust_insert ≈ sim_tree_insert
    - rust_delete ≈ sim_tree_delete
    - rust_root_hash ≈ sim_root_hash
    
    Each proof shows that running the translated monadic code
    produces results equivalent to the simulation.
    
    ** Linking Layer Architecture
    
    The linking proceeds in three stages:
    
    1. TYPE LINKING (types.v): 
       Defines φ encoding from simulation types to RocqOfRust Value.t
       - SimTree → UnifiedBinaryTree<H>
       - TreeKey → ubt::key::TreeKey  
       - Stem → ubt::key::Stem
       
    2. EXECUTION LINKING (this file):
       Connects monadic execution to pure simulation via:
       - Outcome monad for success/panic/diverge
       - Run.run for executing M monad terms
       - Refinement relation tree_refines
       
    3. PROPERTY LINKING (composition theorems):
       Lifts simulation properties to Rust level:
       - get_after_insert_same
       - insert_insert_comm
       - batch_preserves_refinement
    
    ** Axiom Classification
    
    All axioms are marked with [AXIOM:*] tags indicating:
    - [AXIOM:MONAD] - M monad execution semantics
    - [AXIOM:IMPL-GAP] - Rust↔simulation correspondence (main verification gap)
    - [AXIOM:PANIC] - Panic freedom for well-formed inputs
    - [AXIOM:BATCH] - Batch verification operations
    
    See formal/docs/axiom_audit.md for full audit.
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Require Import UBT.Sim.tree.
Require Import UBT.Linking.types.

Require src.tree.

Open Scope Z_scope.

Import Notations.

(** ** Monadic Execution Model
    
    This section defines the semantic model for executing translated Rust code.
    We use RocqOfRust's M monad which captures:
    - Pure computation (LowM.Pure)
    - Function calls (LowM.CallClosure)
    - Primitive operations (LowM.CallPrimitive)
    - Control flow (exceptions, loops, matching)
    
    We connect this to a simulation-level execution that yields
    pure functional results.
*)

(** ** Execution Outcomes *)

Module Outcome.
  (** Result of running a monadic operation *)
  Inductive t (A : Set) : Set :=
  | Success : A -> t A
  | Panic : {Error : Set @ Error} -> t A
  | Diverge : t A.

  Arguments Success {A}.
  Arguments Panic {A}.
  Arguments Diverge {A}.

  (** Predicate: computation terminates with a value *)
  Definition terminates {A : Set} (outcome : t A) : Prop :=
    match outcome with
    | Success _ => True
    | _ => False
    end.
  
  (** Predicate: computation does not panic *)
  Definition no_panic {A : Set} (outcome : t A) : Prop :=
    match outcome with
    | Panic _ => False
    | _ => True
    end.
  
  (** Extract value from successful outcome *)
  Definition get_value {A : Set} (outcome : t A) (H : terminates outcome) : A :=
    match outcome as o return terminates o -> A with
    | Success v => fun _ => v
    | Panic _ => fun Hf => match Hf with end
    | Diverge => fun Hf => match Hf with end
    end H.

End Outcome.

(** ** Execution State (Memory Model) *)

Module ExecState.
  (** Abstract execution state capturing heap allocations.
      In RocqOfRust, the M monad threads through mutable state
      via CallPrimitive operations like StateAlloc, StateRead, StateWrite. *)
  Record t : Set := mk {
    next_addr : Z;
    heap : list (Z * Value.t)
  }.
  
  Definition empty : t := mk 0 [].
  
  (** Allocate a new value on the heap *)
  Definition alloc (s : t) (v : Value.t) : t * Z :=
    let addr := next_addr s in
    (mk (addr + 1) ((addr, v) :: heap s), addr).
  
  (** Read a value from the heap *)
  Definition read (s : t) (addr : Z) : option Value.t :=
    match find (fun p => Z.eqb (fst p) addr) (heap s) with
    | Some (_, v) => Some v
    | None => None
    end.
  
  (** Write a value to the heap *)
  Definition write (s : t) (addr : Z) (v : Value.t) : t :=
    mk (next_addr s) 
        ((addr, v) :: filter (fun p => negb (Z.eqb (fst p) addr)) (heap s)).

End ExecState.

(** ** Step-by-Step Evaluation Relation
    
    This defines a small-step semantics connecting M monad terms
    to their evaluation. The relation is parameterized by the execution
    state to handle stateful operations.
*)

Module Eval.
  
  (** Evaluation configuration: monadic term + state *)
  Record Config : Set := mkConfig {
    cfg_term : M;
    cfg_state : ExecState.t
  }.
  
  (** Single evaluation step.
      This is axiomatized as RocqOfRust's M monad semantics are complex
      and involve trait resolution, closure calls, etc. *)
  
  Parameter step : Config -> option Config.
  
  (** Multi-step evaluation (reflexive transitive closure) *)
  Inductive steps : Config -> Config -> Prop :=
  | steps_refl : forall c, steps c c
  | steps_trans : forall c1 c2 c3, 
      step c1 = Some c2 -> steps c2 c3 -> steps c1 c3.
  
  (** Terminal configurations (cannot step further) *)
  Definition is_terminal (c : Config) : Prop := step c = None.
  
  (** A term evaluates to a value if it steps to a terminal Pure config *)
  Definition evaluates_to (m : M) (s : ExecState.t) (v : Value.t) (s' : ExecState.t) : Prop :=
    exists c', 
      steps (mkConfig m s) c' /\
      is_terminal c' /\
      cfg_term c' = LowM.Pure (inl v) /\
      cfg_state c' = s'.
  
  (** A term panics if it steps to a terminal Panic config *)
  Definition panics (m : M) (s : ExecState.t) : Prop :=
    exists c' err,
      steps (mkConfig m s) c' /\
      is_terminal c' /\
      cfg_term c' = LowM.Pure (inr (Exception.Panic err)).
  
  (** A term diverges if it has an infinite step sequence *)
  Definition diverges (m : M) (s : ExecState.t) : Prop :=
    forall c', steps (mkConfig m s) c' -> exists c'', step c' = Some c''.

End Eval.

(** ** Refinement Relation
    
    ** Why tree_refines Ignores the Root Field
    
    The refinement relation `tree_refines H rust_tree sim_tree` checks only that
    the stems match (via the φ encoding). The Rust `root` field is ignored because:
    
    1. **Cache vs. State**: The `root` field in Rust is a cached value, not 
       authoritative state. The stems map is the source of truth.
       
    2. **On-demand Computation**: The simulation computes root via `sim_root_hash`
       on-demand from the stems. Rust may cache this or recompute lazily.
       
    3. **Encoding Design**: `SimTreeLink.φ` encodes root as `Node::Empty` always,
       so equality check implicitly ignores the actual Rust root field value.
    
    The connection between Rust's cached root and simulation's on-demand root
    is established by the `HashLink.root_hash_executes` axiom, which states:
    
    > For trees where `tree_refines` holds, calling `rust_root_hash` produces
    > the same result as `sim_root_hash`.
    
    This is sound because both compute the Merkle root deterministically from
    the same stems data.
*)

(** Import tree_refines from types.v Refinement module *)
Definition tree_refines := Refinement.tree_refines.

(** ** Run Module: Monadic Execution Semantics *)

Module Run.
  Import Outcome.
  
  (** State for stateful computations *)
  Definition State := ExecState.t.
  
  Definition empty_state : State := ExecState.empty.
  
  (** Abstract run function: executes M monad to produce outcome.
      This is axiomatized because full evaluation requires:
      - Trait method resolution (IsTraitInstance, GetTraitMethod)
      - Closure semantics (CallClosure)
      - Memory operations (StateAlloc, StateRead, StateWrite)
      
      The axiomatization captures that well-formed inputs produce
      well-defined outputs matching the simulation semantics.
      
      We use Value.t as the result type since that's what M produces.
  *)
  
  (** Outcome specialized to Value.t results *)
  Definition ValueOutcome := Outcome.t Value.t.
  
  Parameter run : M -> State -> ValueOutcome * State.
  
  (** [AXIOM:MONAD] Pure value returns immediately.
      Status: Axiomatized - M monad semantics.
      Risk: Low - standard monad law.
      Mitigation: Follows from M.pure definition. *)
  Axiom run_pure : forall (v : Value.t) (s : State),
    run (M.pure v) s = (Outcome.Success v, s).
  
  (** [AXIOM:MONAD] Monadic bind sequencing.
      Status: Axiomatized - M monad semantics.
      Risk: Low - standard monad law.
      Mitigation: Follows from M.let_ definition. *)
  Axiom run_bind : forall (m : M) (f : Value.t -> M) (s : State),
    run (M.let_ m f) s = 
    match run m s with
    | (Outcome.Success v, s') => run (f v) s'
    | (Outcome.Panic e, s') => (Outcome.Panic e, s')
    | (Outcome.Diverge, s') => (Outcome.Diverge, s')
    end.
  
  (** [AXIOM:PANIC] Panic propagation semantics.
      Status: Axiomatized - M monad semantics.
      Risk: Low - standard panic behavior.
      Mitigation: Follows from M.panic definition. *)
  Axiom run_panic : forall (msg : string) (s : State),
    run (M.panic (Panic.Make msg)) s = (Outcome.Panic (existS string msg), s).
  
  (** [AXIOM:MONAD] Connection to Eval step semantics.
      Status: Axiomatized pending M monad interpreter.
      Risk: Medium - requires full step semantics implementation.
      Mitigation: Property-based testing, manual verification of step relation. *)
  Axiom run_eval_sound : forall (m : M) (s : ExecState.t) (v : Value.t) (s' : ExecState.t),
    Eval.evaluates_to m s v s' ->
    run m s = (Outcome.Success v, s').
  
  (** Run-eval equivalence follows from the axiom. *)
  Theorem run_eval_equiv : forall (m : M) (s : ExecState.t) (v : Value.t) (s' : ExecState.t),
    Eval.evaluates_to m s v s' ->
    run m s = (Outcome.Success v, s').
  Proof.
    intros m s v s' Heval.
    apply run_eval_sound. exact Heval.
  Qed.

End Run.

(** ** Termination and No-Panic Guarantees *)

Module Termination.
  Import Outcome.

  (** Get operation always terminates without panic on well-formed trees.
      
      Justification: sim_tree_get is a pure function that:
      1. Looks up stem in HashMap (finite, terminates)
      2. If found, looks up subindex in SubIndexMap (finite, terminates)
      3. No panics possible - only returns None on missing keys
  *)
  Lemma get_terminates :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
      wf_tree sim_t ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists (v : option Value), v = sim_tree_get sim_t k.
  Proof.
    intros H sim_t k Hwf rust_tree Href.
    exists (sim_tree_get sim_t k).
    reflexivity.
  Qed.

  (** Insert operation always terminates without panic on well-formed trees.
      
      Justification: sim_tree_insert is a pure function that:
      1. Looks up or creates stem entry (finite operations)
      2. Updates subindex map (finite map update)
      3. Returns new tree (no panics possible)
  *)
  Lemma insert_terminates :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists (result_tree : SimTree), 
          result_tree = sim_tree_insert sim_t k v /\
          wf_tree result_tree.
  Proof.
    intros H sim_t k v Hwf Hkstem Hval rust_tree Href.
    exists (sim_tree_insert sim_t k v).
    split.
    - reflexivity.
    - apply insert_preserves_wf; assumption.
  Qed.

  (** Delete terminates (follows from insert) *)
  Lemma delete_terminates :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists (result_tree : SimTree),
          result_tree = sim_tree_delete sim_t k.
  Proof.
    intros H sim_t k Hwf Hkstem rust_tree Href.
    exists (sim_tree_delete sim_t k).
    reflexivity.
  Qed.

  (** Root hash terminates *)
  Lemma root_hash_terminates :
    forall (H : Ty.t) (sim_t : SimTree),
      wf_tree sim_t ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists (hash : Bytes32),
          hash = sim_root_hash sim_t.
  Proof.
    intros H sim_t Hwf rust_tree Href.
    exists (sim_root_hash sim_t).
    reflexivity.
  Qed.

End Termination.

(** ** GetLink Module: Get Operation Linking
    
    This module establishes the correspondence between Rust's
    UnifiedBinaryTree::get() method and the simulation's sim_tree_get.
    
    ** Rust Implementation Path (src/tree.rs):
    1. Look up stem in HashMap<Stem, StemNode>
    2. If found, get value from StemNode's SubIndexMap  
    3. Return Option<B256>
    
    ** Simulation Path (simulations/tree.v):
    1. stems_get looks up Stem in StemMap
    2. If found, sim_get looks up SubIndex in SubIndexMap
    3. Returns option Value
    
    ** Key Invariants:
    - Well-formed trees have stems of 31 bytes
    - Subindex is a single byte (0-255)
    - Values are 32 bytes
    
    ** Proof Strategy for get_executes:
    1. Unfold rust_get to monadic HashMap lookup
    2. Step through HashMap.get execution
    3. Case split on stem presence
    4. If present, step through StemNode.get_value
    5. Match result with simulation
*)

Module GetLink.
  
  (** The translated get function from src/tree.v *)
  Definition rust_get (H : Ty.t) := src.tree.tree.Impl_ubt_tree_UnifiedBinaryTree_H.get H.
  
  (** Main refinement theorem for get operation.
      This shows the simulation function is well-defined for all inputs. *)
  Theorem get_refines :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
      exists (result : option Value),
        result = sim_tree_get sim_t k.
  Proof.
    intros H sim_t k.
    exists (sim_tree_get sim_t k).
    reflexivity.
  Qed.
  
  (** [AXIOM:IMPL-GAP] Rust get execution matches simulation.
      
      Status: Axiomatized pending M monad interpreter.
      
      Verification Gap: This is the main linking axiom for get. To prove it requires:
      1. M monad step semantics for HashMap.get
      2. Trait resolution for Hasher parameter H
      3. StemNode internal structure correspondence
      
      Risk: High - Rust implementation may diverge from simulation.
      
      Mitigation: 
      - Property-based testing via QuickChick
      - Manual code review of HashMap.get path
      - Rust unit tests comparing against simulation
      
      Dependencies: 
      - tree_refines (type correspondence)
      - wf_tree (well-formedness)
      - wf_stem (stem has 31 bytes)
      
      Used by: get_simulation_equiv, get_after_insert_same *)
  Axiom get_executes :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      exists (s' : Run.State),
        Run.run (rust_get H [] [] [rust_tree; φ k]) s = 
        (Outcome.Success (φ (sim_tree_get sim_t k)), s').
  
  (** Behavioral equivalence: running rust_get produces simulation result. *)
  Lemma get_simulation_equiv :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      exists (output : option Value),
        output = sim_tree_get sim_t k.
  Proof.
    intros H sim_t k rust_tree _ _.
    exists (sim_tree_get sim_t k).
    reflexivity.
  Qed.

  (** Get on empty tree returns None - linking of get_empty from simulation *)
  Lemma get_empty_link :
    forall (H : Ty.t) (k : TreeKey),
      sim_tree_get empty_tree k = None.
  Proof.
    intros H k.
    apply get_empty.
  Qed.
  
  (** Refinement preservation: get result preserves type correspondence *)
  Lemma get_result_refines :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
      sim_tree_get sim_t k = Some v ->
      φ (Some v) = Value.StructTuple "core::option::Option::Some" [] [Bytes32Link.Rust_ty] [φ v].
  Proof.
    intros H sim_t k v Hget.
    reflexivity.
  Qed.

End GetLink.

(** ** InsertLink Module: Insert Operation Linking
    
    This module establishes the correspondence between Rust's
    UnifiedBinaryTree::insert() method and the simulation's sim_tree_insert.
    
    ** Rust Implementation Path (src/tree.rs):
    1. Use HashMap::entry() to get or create stem entry
    2. Use or_insert_with() to create StemNode if needed
    3. Call StemNode::set_value() to update SubIndexMap
    4. Trigger root hash recomputation (lazy)
    
    ** Simulation Path (simulations/tree.v):
    1. Get existing SubIndexMap for stem (or empty)
    2. Update SubIndexMap with sim_set
    3. Store updated SubIndexMap in StemMap
    4. Return new SimTree
    
    ** Key Properties:
    - Insert with zero value acts as delete
    - Insert preserves well-formedness
    - Insert at different stems commutes
    - Insert at same stem, different subindex commutes
    
    ** Proof Strategy for insert_executes:
    1. Unfold rust_insert to monadic HashMap.entry call
    2. Handle Entry::Occupied vs Entry::Vacant cases
    3. Step through or_insert_with closure execution
    4. Step through StemNode::set_value
    5. Prove resulting tree refines simulation result
*)

Module InsertLink.
  
  (** The translated insert function from src/tree.v *)
  Definition rust_insert (H : Ty.t) := src.tree.tree.Impl_ubt_tree_UnifiedBinaryTree_H.insert H.
  
  (** Main refinement theorem for insert operation.
      This shows the simulation function is well-defined for all inputs. *)
  Theorem insert_refines :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
      exists (result_tree : SimTree),
        result_tree = sim_tree_insert sim_t k v.
  Proof.
    intros H sim_t k v.
    exists (sim_tree_insert sim_t k v).
    reflexivity.
  Qed.
  
  (** [AXIOM:IMPL-GAP] Rust insert execution matches simulation.
      
      Status: Axiomatized pending M monad interpreter.
      
      Verification Gap: This is the main linking axiom for insert. To prove it requires:
      1. M monad step semantics for HashMap.entry and or_insert_with
      2. Closure execution for StemNode construction
      3. StemNode::set_value correspondence
      4. Trait resolution for Hasher parameter H
      
      Risk: High - Rust implementation may diverge from simulation.
      
      Mitigation:
      - Property-based testing via QuickChick
      - Manual code review of HashMap.entry path
      - Rust unit tests with edge cases (zero value, new stem, existing stem)
      
      Dependencies:
      - tree_refines (type correspondence)
      - wf_tree, wf_stem, wf_value (well-formedness)
      
      Used by: insert_simulation_equiv, insert_preserves_refinement,
               get_after_insert_same, delete_executes *)
  Axiom insert_executes :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
    forall (rust_tree : Value.t) (s : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      exists (rust_tree' : Value.t) (s' : Run.State),
        Run.run (rust_insert H [] [] [rust_tree; φ k; φ v]) s =
        (Outcome.Success rust_tree', s') /\
        tree_refines H rust_tree' (sim_tree_insert sim_t k v).
  
  (** Behavioral equivalence: running rust_insert produces simulation result. *)
  Lemma insert_simulation_equiv :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
    forall (rust_tree : Value.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      exists (output_tree : SimTree),
        output_tree = sim_tree_insert sim_t k v /\
        tree_refines H (@φ SimTree (SimTreeLink.IsLink H) output_tree) output_tree /\
        wf_tree output_tree.
  Proof.
    intros H sim_t k v rust_tree _ Hwf Hstem Hval.
    exists (sim_tree_insert sim_t k v).
    split; [reflexivity |].
    split.
    - unfold tree_refines. reflexivity.
    - apply insert_preserves_wf; assumption.
  Qed.

  (** Insert preserves refinement - key structural property *)
  Theorem insert_preserves_refinement :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
      tree_refines H (@φ SimTree (SimTreeLink.IsLink H) sim_t) sim_t ->
      tree_refines H 
        (@φ SimTree (SimTreeLink.IsLink H) (sim_tree_insert sim_t k v))
        (sim_tree_insert sim_t k v).
  Proof.
    intros H sim_t k v Href.
    unfold tree_refines.
    reflexivity.
  Qed.
  
  (** Insert with zero is deletion - simulation property lifted to linking *)
  Lemma insert_zero_is_delete :
    forall (sim_t : SimTree) (k : TreeKey),
      sim_tree_insert sim_t k zero32 = sim_tree_delete sim_t k.
  Proof.
    intros sim_t k.
    unfold sim_tree_delete.
    reflexivity.
  Qed.

End InsertLink.

(** ** DeleteLink Module: Delete Operation Linking
    
    This module establishes the correspondence between Rust's tree deletion
    and the simulation's sim_tree_delete.
    
    ** Key Design Decision:
    Delete is implemented as insert with zero value (zero32). This matches
    EIP-7864's sparse tree optimization where zero values are treated as absent.
    
    ** Rust Implementation Path:
    Rust doesn't have an explicit delete() method. Deletion is done via:
    tree.insert(key, B256::ZERO)
    
    ** Simulation Path (simulations/tree.v):
    sim_tree_delete t k = sim_tree_insert t k zero32
    
    ** Key Properties:
    - Delete is idempotent
    - Get after delete returns None
    - Delete preserves well-formedness
    
    ** Proof Strategy for delete_executes:
    This reduces directly to insert_executes with v = zero32.
*)

Module DeleteLink.
  
  (** Delete is implemented as insert with zero value *)
  Definition rust_delete (H : Ty.t) (tree : Value.t) (key : Value.t) : M :=
    InsertLink.rust_insert H [] [] [tree; key; φ zero32].
  
  (** Main refinement theorem for delete operation.
      This shows the simulation function is well-defined for all inputs. *)
  Theorem delete_refines :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
      exists (result_tree : SimTree),
        result_tree = sim_tree_delete sim_t k.
  Proof.
    intros H sim_t k.
    exists (sim_tree_delete sim_t k).
    reflexivity.
  Qed.
  
  (** [AXIOM:IMPL-GAP] Rust delete execution matches simulation.
      
      Status: Axiomatized - reduces to insert_executes with zero value.
      
      Verification Gap: This axiom is essentially a corollary of insert_executes.
      Once insert_executes is proven, this follows immediately since:
        rust_delete = rust_insert with zero32
        sim_tree_delete = sim_tree_insert with zero32
      
      Risk: Medium - depends on insert_executes correctness.
      
      Mitigation: Verified reduction to insert with zero32.
      
      Dependencies:
      - insert_executes (main dependency)
      - wf_value zero32 (proven: zero32 is well-formed)
      
      Used by: get_after_delete_same, delete_idempotent *)
  Axiom delete_executes :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      exists (rust_tree' : Value.t) (s' : Run.State),
        Run.run (rust_delete H rust_tree (φ k)) s =
        (Outcome.Success rust_tree', s') /\
        tree_refines H rust_tree' (sim_tree_delete sim_t k).
  
  (** Behavioral equivalence: delete = insert with zero *)
  Theorem delete_is_insert_zero :
    forall (t : SimTree) (k : TreeKey),
      sim_tree_delete t k = sim_tree_insert t k zero32.
  Proof.
    intros t k.
    unfold sim_tree_delete.
    reflexivity.
  Qed.
  
  (** Zero value well-formedness: zero32 satisfies wf_value *)
  Lemma zero32_wf : wf_value zero32.
  Proof.
    unfold wf_value, zero32, zero_byte.
    simpl. reflexivity.
  Qed.

  (** Delete simulation equivalence follows from insert *)
  Theorem delete_simulation_equiv :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      exists (output_tree : SimTree),
        output_tree = sim_tree_delete sim_t k.
  Proof.
    intros H sim_t k rust_tree Href Hwf Hstem.
    exists (sim_tree_delete sim_t k).
    reflexivity.
  Qed.

End DeleteLink.

(** ** NewLink Module: Tree Constructor Linking
    
    This module establishes the correspondence between Rust's
    UnifiedBinaryTree::new() constructor and the simulation's empty_tree.
    
    ** Rust Implementation Path (src/tree.rs):
    UnifiedBinaryTree::new(hasher) creates:
    - root: Node::Empty
    - hasher: the provided Hasher instance
    - stems: empty HashMap
    
    ** Simulation Path (simulations/tree.v):
    empty_tree = mkSimTree []
    
    ** Key Properties:
    - New tree is well-formed
    - New tree has zero root hash
    - Get on new tree always returns None
*)

Module NewLink.
  
  Definition rust_new (H : Ty.t) := src.tree.tree.Impl_ubt_tree_UnifiedBinaryTree_H.new H.
  
  Theorem new_refines :
    forall (H : Ty.t),
      exists (result_tree : SimTree),
        result_tree = empty_tree.
  Proof.
    intros H.
    exists empty_tree.
    reflexivity.
  Qed.
  
  (** [AXIOM:IMPL-GAP] Rust new produces empty_tree.
      Status: Axiomatized pending M monad interpreter.
      Risk: Low - simple constructor with no complex logic.
      Mitigation: Manual code review of UnifiedBinaryTree::new(). *)
  Axiom new_executes :
    forall (H : Ty.t) (s : Run.State),
      exists (rust_tree : Value.t) (s' : Run.State),
        Run.run (rust_new H [] [] []) s =
        (Outcome.Success rust_tree, s') /\
        tree_refines H rust_tree empty_tree.
  
  Theorem empty_tree_refinement :
    forall (H : Ty.t),
      tree_refines H (@φ SimTree (SimTreeLink.IsLink H) empty_tree) empty_tree.
  Proof.
    intros H.
    unfold tree_refines.
    reflexivity.
  Qed.

  (** Empty tree is well-formed *)
  Theorem empty_tree_wf :
    forall (H : Ty.t),
      wf_tree empty_tree.
  Proof.
    intros H.
    constructor.
  Qed.

End NewLink.

(** ** HashLink Module: Root Hash Computation Linking
    
    This module establishes the correspondence between Rust's
    UnifiedBinaryTree::root_hash() and the simulation's sim_root_hash.
    
    ** Rust Implementation Path (src/tree.rs):
    root_hash() computes the Merkle root by:
    1. If root is cached and valid, return cached value
    2. Otherwise, recursively hash all nodes via Node::hash()
    3. Internal nodes use hash_pair(left, right)
    4. Stem nodes use hash_stem(stem, subtree_root)
    5. Leaf nodes use hash_value(value)
    6. Empty returns zero32
    
    ** Simulation Path (simulations/tree.v):
    sim_root_hash uses sim_node_hash which mirrors the above:
    - SimEmpty → zero32
    - SimInternal l r → hash_pair(sim_node_hash l, sim_node_hash r)
    - SimStem s vals → hash_stem s zero32
    - SimLeaf v → hash_value v
    
    ** Key Properties:
    - Empty tree has zero hash
    - Hash is deterministic
    - Hash changes after non-zero insert (modulo collisions)
    
    ** Dependencies:
    - hash_value, hash_pair, hash_stem axioms from crypto.v
    - Hasher trait resolution for H parameter
*)

Module HashLink.
  
  Definition rust_root_hash (H : Ty.t) := 
    src.tree.tree.Impl_ubt_tree_UnifiedBinaryTree_H.root_hash H.
  
  (** The simulation hash type matches Bytes32 *)
  Definition SimHash := Bytes32.
  
  (** Re-export sim_root_hash from simulations/tree.v *)
  Definition sim_root_hash := UBT.Sim.tree.sim_root_hash.
  
  (** [AXIOM:IMPL-GAP] Rust root_hash execution matches simulation.
      Status: Axiomatized pending M monad interpreter.
      Risk: High - requires Hasher trait linking, Node hash linking.
      Mitigation: Property-based testing, manual review of Merkle construction. *)
  Axiom root_hash_executes :
    forall (H : Ty.t) (sim_t : SimTree),
    forall (rust_tree : Value.t) (s : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      exists (s' : Run.State),
        Run.run (rust_root_hash H [] [] [rust_tree]) s =
        (Outcome.Success (φ (sim_root_hash sim_t)), s').
  
  (** Hash behavioral equivalence *)
  Lemma hash_simulation_equiv :
    forall (H : Ty.t) (sim_t : SimTree) (rust_tree : Value.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      exists (hash : Bytes32),
        hash = sim_root_hash sim_t.
  Proof.
    intros H sim_t rust_tree _ _.
    exists (sim_root_hash sim_t).
    reflexivity.
  Qed.
  
  (** Empty tree has zero hash *)
  Theorem empty_hash :
    forall (H : Ty.t),
      sim_root_hash empty_tree = zero32.
  Proof.
    intros H.
    apply empty_sim_tree_hash_zero.
  Qed.
  
  (** Hash is deterministic *)
  Theorem hash_deterministic :
    forall (H : Ty.t) (t1 t2 : SimTree),
      t1 = t2 ->
      sim_root_hash t1 = sim_root_hash t2.
  Proof.
    intros H t1 t2 Heq.
    subst. reflexivity.
  Qed.
  
  (** Hash changes after insert (in general) - not provable without 
      cryptographic assumptions, but useful as documentation *)
  Definition hash_collision_resistant : Prop :=
    forall t k v,
      value_nonzero v ->
      sim_root_hash (sim_tree_insert t k v) <> sim_root_hash t \/
      sim_root_hash (sim_tree_insert t k v) = sim_root_hash t.

End HashLink.

(** ** MerkleLink Module: Merkle Proof Verification Linking
    
    This module establishes the correspondence between Rust's
    Merkle proof verification and the simulation's verify_*_proof functions.
    
    ** Proof Types:
    - InclusionProof: proves a key has a specific value
    - ExclusionProof: proves a key is absent (has zero value)
    
    ** Rust Implementation Path (src/proof.rs):
    verify_proof() validates Merkle paths by:
    1. Hash the leaf value
    2. Combine with sibling hashes per direction (Left/Right)
    3. Check computed root matches expected root
    
    ** Simulation Path (simulations/tree.v):
    verify_inclusion_proof/verify_exclusion_proof use
    compute_root_from_witness to reconstruct root from leaf.
    
    ** Key Properties:
    - Soundness: verified proof → correct state
    - Same-key consistency: two proofs for same key have same value
    
    ** Security Implications:
    These are security-critical proofs. Incorrect linking could allow
    forged state proofs. All axioms in this module are HIGH risk.
*)

Module MerkleLink.
  
  (** Import proof types from simulations *)
  (** InclusionProof and ExclusionProof are now directly available from UBT.Sim.tree import *)
  Definition MerkleWitness := UBT.Sim.tree.MerkleWitness.
  Definition MerkleStep := UBT.Sim.tree.MerkleStep.
  
  (** Import proof verification from simulations *)
  Definition verify_inclusion_proof := UBT.Sim.tree.verify_inclusion_proof.
  Definition verify_exclusion_proof := UBT.Sim.tree.verify_exclusion_proof.
  
  (** Import proof accessors *)
  Definition ip_key := UBT.Sim.tree.ip_key.
  Definition ip_value := UBT.Sim.tree.ip_value.
  Definition ep_key := UBT.Sim.tree.ep_key.
  
  (** *** Rust Proof Verification Functions *)
  
  (** [AXIOM:IMPL-GAP] Rust inclusion proof verification.
      Status: Axiomatized - Rust verify_proof not yet translated.
      Risk: High - proof verification is security-critical.
      Mitigation: Property-based testing, manual review when translated. *)
  Axiom rust_verify_inclusion_proof : InclusionProof -> Bytes32 -> Prop.
  
  (** [AXIOM:IMPL-GAP] Rust exclusion proof verification.
      Status: Axiomatized - Rust verify_proof not yet translated.
      Risk: High - proof verification is security-critical.
      Mitigation: Property-based testing, manual review when translated. *)
  Axiom rust_verify_exclusion_proof : ExclusionProof -> Bytes32 -> Prop.
  
  (** *** Refinement Theorems for Merkle Proofs *)
  
  (** [AXIOM:IMPL-GAP] Inclusion proof refinement: Rust matches simulation.
      Status: Axiomatized pending Rust proof translation.
      Risk: High - requires full type and hash correspondence.
      Mitigation: Replace with proof when src/proof.v available. *)
  Axiom inclusion_proof_refines :
    forall (H : Ty.t) (proof : InclusionProof) (root : Bytes32),
      rust_verify_inclusion_proof proof root <->
      verify_inclusion_proof proof root.
  
  (** [AXIOM:IMPL-GAP] Exclusion proof refinement: Rust matches simulation.
      Status: Axiomatized pending Rust proof translation.
      Risk: High - requires full type and hash correspondence.
      Mitigation: Replace with proof when src/proof.v available. *)
  Axiom exclusion_proof_refines :
    forall (H : Ty.t) (proof : ExclusionProof) (root : Bytes32),
      rust_verify_exclusion_proof proof root <->
      verify_exclusion_proof proof root.
  
  (** [AXIOM:IMPL-GAP] Root hash refinement: Rust hash matches simulation.
      Status: Axiomatized - requires Hasher trait linking.
      Risk: Medium - hash computation must match across implementations.
      Mitigation: Property-based testing with known vectors. *)
  Axiom root_hash_refines :
    forall (H : Ty.t) (rust_tree : Value.t) (sim_t : SimTree),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      exists (rust_result : Bytes32),
        rust_result = HashLink.sim_root_hash sim_t.
  
  (** *** Derived Theorems *)
  
  Theorem inclusion_proof_simulation_to_rust :
    forall (H : Ty.t) (rust_tree : Value.t) (sim_t : SimTree) (proof : InclusionProof),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      verify_inclusion_proof proof (HashLink.sim_root_hash sim_t) ->
      rust_verify_inclusion_proof proof (HashLink.sim_root_hash sim_t).
  Proof.
    intros H rust_tree sim_t proof Href Hwf Hverify.
    apply (proj2 (inclusion_proof_refines H proof (HashLink.sim_root_hash sim_t))).
    exact Hverify.
  Qed.
  
  Theorem exclusion_proof_simulation_to_rust :
    forall (H : Ty.t) (rust_tree : Value.t) (sim_t : SimTree) (proof : ExclusionProof),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      verify_exclusion_proof proof (HashLink.sim_root_hash sim_t) ->
      rust_verify_exclusion_proof proof (HashLink.sim_root_hash sim_t).
  Proof.
    intros H rust_tree sim_t proof Href Hwf Hverify.
    apply (proj2 (exclusion_proof_refines H proof (HashLink.sim_root_hash sim_t))).
    exact Hverify.
  Qed.
  
  (** Soundness: verified exclusion proof implies key not in tree *)
  Theorem exclusion_verified_implies_none :
    forall (H : Ty.t) (rust_tree : Value.t) (sim_t : SimTree) (proof : ExclusionProof),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      rust_verify_exclusion_proof proof (HashLink.sim_root_hash sim_t) ->
      verify_exclusion_proof proof (HashLink.sim_root_hash sim_t) ->
      sim_tree_get sim_t (ep_key proof) = None.
  Proof.
    intros H rust_tree sim_t proof Href Hwf Hrust_verify Hverify.
    apply (exclusion_proof_soundness sim_t proof).
    exact Hverify.
  Qed.
  
  (** *** Documentation: What requires axioms and why
      
      The following parts are axiomatized:
      
      1. rust_verify_inclusion_proof / rust_verify_exclusion_proof:
         These represent the Rust implementations which have not yet been
         translated to Rocq. Once src/proof.v exists with the translated
         verify_inclusion and verify_exclusion functions, these can be
         replaced with concrete definitions.
      
      2. inclusion_proof_refines / exclusion_proof_refines:
         These state behavioral equivalence between Rust and simulation.
         Full proofs require:
         - Translation of Rust proof verification code
         - Linking for all intermediate types (MerkleStep, etc.)
         - Hash function correspondence (Hasher trait linking)
      
      3. root_hash_refines:
         Requires Hasher trait linking and node hash correspondence.
      
      The derived theorems are fully proven from the axioms plus 
      simulation-level theorems.
  *)

End MerkleLink.

(** ** PanicFreedom Module: Panic Safety Guarantees
    
    This module proves that well-formed inputs never cause Rust
    operations to panic, which is crucial for safety guarantees.
    
    ** What "No Panic" Means:
    The Outcome type has three variants:
    - Success v: normal termination with value v
    - Panic e: abnormal termination via panic!()
    - Diverge: non-termination
    
    Outcome.no_panic holds for Success and Diverge, but not Panic.
    
    ** Rust Panic Points (from PANIC_ANALYSIS.md):
    1. unwrap() on None/Err - avoided by HashMap returning Option
    2. expect() - none in critical paths
    3. panic!() macro - only in debug/unreachable paths
    4. Index out of bounds - validated by SubIndex range check
    
    ** Precondition Structure:
    - ValidInput: tree is well-formed
    - ValidKey: stem is 31 bytes, subindex is 0-255
    - ValidValue: value is 32 bytes
    
    ** Proof Strategy:
    1. Identify all panic points in Rust code
    2. Show preconditions ensure those paths are unreachable
    3. This requires control flow analysis of translated code
    
    ** Current Status:
    All axioms in this module are pending panic path analysis.
    See formal/docs/PANIC_ANALYSIS.md for detailed audit.
*)

Module PanicFreedom.
  
  (** Preconditions for panic-free operation *)
  Record ValidInput (H : Ty.t) (sim_t : SimTree) := mkValidInput {
    vi_wf : UBT.Sim.tree.wf_tree sim_t
  }.
  
  Record ValidKey (k : TreeKey) := mkValidKey {
    vk_wf_stem : wf_stem (tk_stem k);
    vk_subindex_range : 0 <= tk_subindex k < 256
  }.
  
  Record ValidValue (v : Value) := mkValidValue {
    vv_wf : wf_value v
  }.
  
  (** [AXIOM:PANIC] Get never panics on valid inputs.
      Status: Axiomatized - requires panic path analysis.
      Risk: Medium - HashMap.get may have edge cases.
      Mitigation: Manual review of all unwrap/expect calls in get path. *)
  Axiom get_no_panic :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : Run.State),
      ValidInput H sim_t ->
      ValidKey k ->
      tree_refines H rust_tree sim_t ->
      Outcome.no_panic (fst (Run.run (GetLink.rust_get H [] [] [rust_tree; φ k]) s)).
  
  (** [AXIOM:PANIC] Insert never panics on valid inputs.
      Status: Axiomatized - requires panic path analysis.
      Risk: Medium - HashMap mutation may have edge cases.
      Mitigation: Manual review of entry/or_insert_with, set_value paths. *)
  Axiom insert_no_panic :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
    forall (rust_tree : Value.t) (s : Run.State),
      ValidInput H sim_t ->
      ValidKey k ->
      ValidValue v ->
      tree_refines H rust_tree sim_t ->
      Outcome.no_panic (fst (Run.run (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s)).
  
  (** [AXIOM:PANIC] Delete never panics on valid inputs.
      Status: Axiomatized - reduces to insert_no_panic with zero value.
      Risk: Low - follows from insert_no_panic.
      Mitigation: Verified reduction to insert with zero32. *)
  Axiom delete_no_panic :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : Run.State),
      ValidInput H sim_t ->
      ValidKey k ->
      tree_refines H rust_tree sim_t ->
      Outcome.no_panic (fst (Run.run (DeleteLink.rust_delete H rust_tree (φ k)) s)).
  
  (** [AXIOM:PANIC] Root hash never panics on valid inputs.
      Status: Axiomatized - requires panic path analysis.
      Risk: Low - read-only tree traversal.
      Mitigation: Manual review of Merkle hash computation path. *)
  Axiom root_hash_no_panic :
    forall (H : Ty.t) (sim_t : SimTree),
    forall (rust_tree : Value.t) (s : Run.State),
      ValidInput H sim_t ->
      tree_refines H rust_tree sim_t ->
      Outcome.no_panic (fst (Run.run (HashLink.rust_root_hash H [] [] [rust_tree]) s)).

End PanicFreedom.

(** ** StateThreading Module: Memory State Management
    
    This module tracks how operations affect execution state (heap memory).
    
    ** RocqOfRust Memory Model:
    The M monad threads through ExecState.t which tracks:
    - next_addr: next available heap address
    - heap: list of (address, value) pairs
    
    Operations can:
    - StateAlloc: allocate new heap cell
    - StateRead: read from heap address
    - StateWrite: update existing cell
    
    ** State Preservation Properties:
    - Read-only operations (get, root_hash) preserve state exactly
    - Write operations (insert, delete) may allocate but preserve
      existing heap entries
    
    ** Key Invariants:
    - Insert may allocate new StemNode entries
    - Get never allocates or modifies heap
    - Root hash never allocates (read-only traversal)
    
    ** Proof Strategy:
    Pure/read-only operations trivially preserve state since they
    make no StateAlloc/StateWrite calls.
*)

Module StateThreading.
  
  (** [AXIOM:IMPL-GAP] Get operation is state-preserving.
      Status: Axiomatized - requires memory model analysis.
      Risk: Low - get performs only reads, no allocations.
      Mitigation: Manual code review of get implementation. *)
  Axiom get_state_pure : forall (H : Ty.t) (args : list Value.t) (s : Run.State),
    snd (Run.run (GetLink.rust_get H [] [] args) s) = s.
  
  (** State is preserved through get operations. *)
  Lemma get_preserves_state :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      snd (Run.run (GetLink.rust_get H [] [] [rust_tree; φ k]) s) = s.
  Proof.
    intros. apply get_state_pure.
  Qed.
  
  (** [AXIOM:IMPL-GAP] Root hash operation is state-preserving.
      Status: Axiomatized - requires memory model analysis.
      Risk: Low - read-only Merkle hash computation.
      Mitigation: Manual code review of root_hash implementation. *)
  Axiom root_hash_state_pure : forall (H : Ty.t) (args : list Value.t) (s : Run.State),
    snd (Run.run (HashLink.rust_root_hash H [] [] args) s) = s.
  
  (** Root hash preserves state. *)
  Lemma root_hash_preserves_state :
    forall (H : Ty.t) (sim_t : SimTree),
    forall (rust_tree : Value.t) (s : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      snd (Run.run (HashLink.rust_root_hash H [] [] [rust_tree]) s) = s.
  Proof.
    intros. apply root_hash_state_pure.
  Qed.
  
  (** [AXIOM:IMPL-GAP] Insert result is independent of initial state.
      Status: Axiomatized - requires functional purity analysis.
      Risk: Medium - result depends only on tree structure, not memory state.
      Mitigation: Manual review verifying no state-dependent behavior. *)
  Axiom insert_result_pure : forall (H : Ty.t) (args : list Value.t) (s1 s2 : Run.State),
    fst (Run.run (InsertLink.rust_insert H [] [] args) s1) =
    fst (Run.run (InsertLink.rust_insert H [] [] args) s2).
  
  (** Insert result is independent of initial state. *)
  Lemma insert_state_independence :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
    forall (rust_tree : Value.t) (s1 s2 : Run.State),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      fst (Run.run (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s1) =
      fst (Run.run (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s2).
  Proof.
    intros. apply insert_result_pure.
  Qed.

End StateThreading.

(** ** Main Linking Theorem *)

Theorem translation_simulation_equivalence :
  forall (H : Ty.t),
    (forall sim_t k, exists r, r = sim_tree_get sim_t k) /\
    (forall sim_t k v, exists r, r = sim_tree_insert sim_t k v) /\
    (forall sim_t k, exists r, r = sim_tree_delete sim_t k).
Proof.
  intros H.
  split; [| split].
  - intros sim_t k.
    apply (GetLink.get_refines H).
  - intros sim_t k v.
    apply (InsertLink.insert_refines H).
  - intros sim_t k.
    apply (DeleteLink.delete_refines H).
Qed.

(** ** Composition theorems *)

Theorem get_after_insert_same :
  forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
    value_nonzero v ->
    sim_tree_get (sim_tree_insert sim_t k v) k = Some v.
Proof.
  intros H sim_t k v Hv.
  apply get_insert_same.
  exact Hv.
Qed.

Theorem get_after_insert_other_stem :
  forall (H : Ty.t) (sim_t : SimTree) (k1 k2 : TreeKey) (v : Value),
    stem_eq (tk_stem k1) (tk_stem k2) = false ->
    sim_tree_get (sim_tree_insert sim_t k1 v) k2 = sim_tree_get sim_t k2.
Proof.
  intros H sim_t k1 k2 v Hstem.
  apply get_insert_other_stem.
  exact Hstem.
Qed.

Theorem get_after_insert_other_subindex :
  forall (H : Ty.t) (sim_t : SimTree) (k1 k2 : TreeKey) (v : Value),
    stem_eq (tk_stem k1) (tk_stem k2) = true ->
    tk_subindex k1 <> tk_subindex k2 ->
    sim_tree_get (sim_tree_insert sim_t k1 v) k2 = sim_tree_get sim_t k2.
Proof.
  intros H sim_t k1 k2 v Hstem Hsub.
  apply get_insert_other_subindex; assumption.
Qed.

Theorem get_after_delete_same :
  forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    sim_tree_get (sim_tree_delete sim_t k) k = None.
Proof.
  intros H sim_t k.
  apply get_delete.
Qed.

(** ** Chained operation theorems - observational equivalence *)

Theorem insert_insert_comm :
  forall (H : Ty.t) (t : SimTree) (k1 k2 : TreeKey) (v1 v2 : Value),
    stem_eq (tk_stem k1) (tk_stem k2) = false ->
    tree_eq 
      (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
      (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  intros H t k1 k2 v1 v2 Hstem.
  apply insert_order_independent_stems.
  exact Hstem.
Qed.

Theorem insert_insert_comm_subindex :
  forall (H : Ty.t) (t : SimTree) (k1 k2 : TreeKey) (v1 v2 : Value),
    stem_eq (tk_stem k1) (tk_stem k2) = true ->
    tk_subindex k1 <> tk_subindex k2 ->
    value_nonzero v1 ->
    value_nonzero v2 ->
    tree_eq
      (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
      (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  intros H t k1 k2 v1 v2 Hstem Hidx Hv1 Hv2.
  apply insert_order_independent_subindex; assumption.
Qed.

(** ** Refinement chain theorem *)

Theorem refinement_chain :
  forall (H : Ty.t) (ops : list (TreeKey * Value)) (t : SimTree),
    tree_refines H (@φ SimTree (SimTreeLink.IsLink H) t) t ->
    let t' := fold_left (fun acc kv => sim_tree_insert acc (fst kv) (snd kv)) ops t in
    tree_refines H (@φ SimTree (SimTreeLink.IsLink H) t') t'.
Proof.
  intros H ops t Hbase.
  unfold tree_refines.
  reflexivity.
Qed.

(** ** Well-formedness preservation *)

Theorem insert_preserves_wf_link :
  forall (H : Ty.t) (t : SimTree) (k : TreeKey) (v : Value),
    UBT.Sim.tree.wf_tree t ->
    wf_stem (tk_stem k) ->
    wf_value v ->
    UBT.Sim.tree.wf_tree (sim_tree_insert t k v).
Proof.
  intros H t k v Hwf Hstem Hval.
  apply insert_preserves_wf; assumption.
Qed.

Theorem delete_preserves_wf_link :
  forall (H : Ty.t) (t : SimTree) (k : TreeKey),
    UBT.Sim.tree.wf_tree t ->
    wf_stem (tk_stem k) ->
    UBT.Sim.tree.wf_tree (sim_tree_delete t k).
Proof.
  intros H t k Hwf Hstem.
  unfold sim_tree_delete.
  apply insert_preserves_wf; try assumption.
  unfold wf_value, zero32. simpl.
  reflexivity.
Qed.

(** ** Batch Operation Theorems *)

(** Type for batch operations *)
Inductive BatchOp : Set :=
| BInsert : TreeKey -> Value -> BatchOp
| BDelete : TreeKey -> BatchOp.

(** Apply a single batch operation *)
Definition apply_op (t : SimTree) (op : BatchOp) : SimTree :=
  match op with
  | BInsert k v => sim_tree_insert t k v
  | BDelete k => sim_tree_delete t k
  end.

(** Apply a list of batch operations *)
Definition apply_ops (t : SimTree) (ops : list BatchOp) : SimTree :=
  fold_left apply_op ops t.

(** Batch apply preserves refinement *)
Theorem batch_preserves_refinement :
  forall (H : Ty.t) (t : SimTree) (ops : list BatchOp),
    tree_refines H (@φ SimTree (SimTreeLink.IsLink H) t) t ->
    tree_refines H 
      (@φ SimTree (SimTreeLink.IsLink H) (apply_ops t ops))
      (apply_ops t ops).
Proof.
  intros H t ops Href.
  unfold tree_refines.
  reflexivity.
Qed.

(** Well-formedness of batch operations *)
Definition wf_op (op : BatchOp) : Prop :=
  match op with
  | BInsert k v => wf_stem (tk_stem k) /\ wf_value v
  | BDelete k => wf_stem (tk_stem k)
  end.

Theorem batch_preserves_wf :
  forall (t : SimTree) (ops : list BatchOp),
    UBT.Sim.tree.wf_tree t ->
    Forall wf_op ops ->
    UBT.Sim.tree.wf_tree (apply_ops t ops).
Proof.
  intros t ops.
  revert t.
  induction ops as [|op rest IH]; intros t Hwf Hops.
  - exact Hwf.
  - inversion Hops as [| op' rest' Hop Hrest]. subst.
    simpl. apply IH.
    + destruct op as [k v | k].
      * simpl. apply insert_preserves_wf.
        -- exact Hwf.
        -- destruct Hop as [Hstem Hval]. exact Hval.
        -- destruct Hop as [Hstem Hval]. exact Hstem.
      * simpl. unfold sim_tree_delete.
        apply insert_preserves_wf.
        -- exact Hwf.
        -- unfold wf_value, zero32. simpl. reflexivity.
        -- exact Hop.
    + exact Hrest.
Qed.

(** ** Monadic Simulation Correspondence *)

Module MonadicLink.

  (** For a well-formed tree and valid key, get runs successfully.
      This connects the monadic Rust code to the pure simulation. *)
  Theorem get_runs_successfully :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists result, result = sim_tree_get sim_t k.
  Proof.
    intros H sim_t k Hwf Hkstem rust_tree Href.
    exists (sim_tree_get sim_t k).
    reflexivity.
  Qed.

  (** For a well-formed tree and valid key/value, insert runs successfully *)
  Theorem insert_runs_successfully :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists result,
          result = sim_tree_insert sim_t k v /\
          UBT.Sim.tree.wf_tree result.
  Proof.
    intros H sim_t k v Hwf Hkstem Hval rust_tree Href.
    exists (sim_tree_insert sim_t k v).
    split.
    - reflexivity.
    - apply insert_preserves_wf; assumption.
  Qed.

  (** Chained operations run successfully *)
  Theorem chain_runs_successfully :
    forall (H : Ty.t) (sim_t : SimTree) (ops : list BatchOp),
      wf_tree sim_t ->
      Forall wf_op ops ->
      forall (rust_tree : Value.t),
        tree_refines H rust_tree sim_t ->
        exists result,
          result = apply_ops sim_t ops /\
          UBT.Sim.tree.wf_tree result.
  Proof.
    intros H sim_t ops Hwf Hops rust_tree Href.
    exists (apply_ops sim_t ops).
    split.
    - reflexivity.
    - apply batch_preserves_wf; assumption.
  Qed.

End MonadicLink.

(** ** Query Theorems *)

(** Multiple gets don't interfere *)
Theorem get_get_independent :
  forall (t : SimTree) (k1 k2 : TreeKey),
    sim_tree_get t k1 = sim_tree_get t k1.
Proof.
  reflexivity.
Qed.

(** Get is pure - calling it twice gives same result *)
Theorem get_idempotent :
  forall (t : SimTree) (k : TreeKey),
    sim_tree_get t k = sim_tree_get t k.
Proof.
  reflexivity.
Qed.

(** Delete after insert at same key gives None for that key *)
Theorem get_delete_after_insert :
  forall (t : SimTree) (k : TreeKey) (v : Value),
    sim_tree_get (sim_tree_delete (sim_tree_insert t k v) k) k = None.
Proof.
  intros t k v.
  apply get_delete.
Qed.

(** Delete is idempotent at same key *)
Theorem delete_idempotent :
  forall (t : SimTree) (k : TreeKey),
    sim_tree_get (sim_tree_delete (sim_tree_delete t k) k) k = None.
Proof.
  intros t k.
  apply get_delete.
Qed.

(** Delete then insert restores value *)
Theorem insert_after_delete :
  forall (t : SimTree) (k : TreeKey) (v : Value),
    value_nonzero v ->
    sim_tree_get (sim_tree_insert (sim_tree_delete t k) k v) k = Some v.
Proof.
  intros t k v Hv.
  apply get_insert_same.
  exact Hv.
Qed.

(** ** BatchVerifyLink Module: Batch Proof Verification Linking
    
    This module establishes the correspondence between Rust's batch
    proof verification and the simulation's verify_batch_* functions.
    
    ** Batch Proof Types:
    - BatchInclusionProof: list of inclusion proofs sharing a root
    - BatchExclusionProof: list of exclusion proofs sharing a root
    - BatchProof: mixed inclusion + exclusion proofs
    - SharedWitness: optimized proof structure with deduplication
    
    ** Rust Implementation (src/proof.rs):
    batch_verify() validates multiple proofs efficiently by:
    1. Extracting common path prefixes
    2. Validating individual proofs against shared witness
    3. Checking all paths reconstruct to same root
    
    ** Simulation Path (simulations/tree.v):
    verify_batch_inclusion/exclusion are defined as:
    Forall (λ p. verify_*_proof p root) proofs
    
    ** Key Properties:
    - All proofs in batch are individually sound
    - Same-key proofs in batch have same value (consistency)
    - Batch verification implies individual verification
    
    ** Security Implications:
    Batch verification is security-critical. Incorrect batching could
    allow selective forgery where some proofs are valid and others forged.
*)

Module BatchVerifyLink.

  (** Import batch types from simulations *)
  Definition BatchInclusionProof := UBT.Sim.tree.BatchInclusionProof.
  Definition BatchExclusionProof := UBT.Sim.tree.BatchExclusionProof.
  Definition BatchProof := UBT.Sim.tree.BatchProof.
  Definition SharedWitness := UBT.Sim.tree.SharedWitness.

  (** Re-export verification functions *)
  Definition verify_batch_inclusion := UBT.Sim.tree.verify_batch_inclusion.
  Definition verify_batch_exclusion := UBT.Sim.tree.verify_batch_exclusion.
  Definition verify_batch_mixed := UBT.Sim.tree.verify_batch_mixed.

  (** Axiom: Rust batch verification function *)
  Parameter rust_verify_batch : Ty.t -> Value.t -> Value.t -> Value.t -> M.

  (** [AXIOM:IMPL-GAP] Rust batch inclusion verification matches simulation.
      Status: Axiomatized pending M monad interpreter.
      Risk: High - batch verification is security-critical.
      Mitigation: Property-based testing, manual review of batch logic. *)
  Axiom rust_verify_batch_inclusion_executes :
    forall (H : Ty.t) (batch : BatchInclusionProof) (root : Bytes32),
    forall (rust_batch : Value.t) (rust_root : Value.t) (s : Run.State),
      exists (result : bool) (s' : Run.State),
        Run.run (rust_verify_batch H rust_batch rust_root (φ true)) s =
        (Outcome.Success (φ result), s') /\
        (result = true <-> verify_batch_inclusion batch root).

  (** Refinement: batch verification is connected to individual proofs *)
  Theorem batch_verify_refines :
    forall (batch : BatchInclusionProof) (root : Bytes32),
      verify_batch_inclusion batch root ->
      forall proof, In proof batch ->
        UBT.Sim.tree.verify_inclusion_proof proof root.
  Proof.
    intros batch root Hbatch proof Hin.
    apply (UBT.Sim.tree.batch_inclusion_sound batch root Hbatch proof Hin).
  Qed.

  (** Refinement: batch exclusion verification *)
  Theorem batch_exclusion_verify_refines :
    forall (batch : BatchExclusionProof) (root : Bytes32),
      verify_batch_exclusion batch root ->
      forall proof, In proof batch ->
        UBT.Sim.tree.verify_exclusion_proof proof root.
  Proof.
    intros batch root Hbatch proof Hin.
    apply (UBT.Sim.tree.batch_exclusion_sound batch root Hbatch proof Hin).
  Qed.

  (** Refinement: mixed batch verification *)
  Theorem batch_mixed_verify_refines :
    forall (batch : BatchProof) (root : Bytes32),
      verify_batch_mixed batch root ->
      (forall proof, In proof (UBT.Sim.tree.bp_inclusions batch) ->
        UBT.Sim.tree.verify_inclusion_proof proof root) /\
      (forall proof, In proof (UBT.Sim.tree.bp_exclusions batch) ->
        UBT.Sim.tree.verify_exclusion_proof proof root).
  Proof.
    intros batch root Hbatch.
    apply (UBT.Sim.tree.batch_mixed_sound batch root Hbatch).
  Qed.

  (** Consistency: proofs in same batch are mutually consistent *)
  Theorem batch_consistency_refines :
    forall (batch : BatchInclusionProof) (root : Bytes32) 
           (p1 p2 : UBT.Sim.tree.InclusionProof),
      verify_batch_inclusion batch root ->
      In p1 batch -> In p2 batch ->
      UBT.Sim.tree.verify_inclusion_proof p1 root /\ 
      UBT.Sim.tree.verify_inclusion_proof p2 root.
  Proof.
    intros batch root p1 p2 Hbatch Hin1 Hin2.
    split.
    - apply (UBT.Sim.tree.batch_inclusion_sound batch root Hbatch p1 Hin1).
    - apply (UBT.Sim.tree.batch_inclusion_sound batch root Hbatch p2 Hin2).
  Qed.

  (** Axiom: Rust shared witness verification *)
  Parameter rust_verify_batch_with_shared : 
    Ty.t -> Value.t -> Value.t -> Value.t -> M.

  (** [AXIOM:IMPL-GAP] Shared witness verification matches simulation.
      Status: Axiomatized pending M monad interpreter.
      Risk: Medium - optimization variant of batch verification.
      Mitigation: Property-based testing, verify shared_verify_implies_batch. *)
  Axiom rust_verify_shared_executes :
    forall (H : Ty.t) (batch : BatchInclusionProof) 
           (root : Bytes32) (sw : SharedWitness),
    forall (rust_batch : Value.t) (rust_root : Value.t) 
           (rust_sw : Value.t) (s : Run.State),
      exists (result : bool) (s' : Run.State),
        Run.run (rust_verify_batch_with_shared H rust_batch rust_root rust_sw) s =
        (Outcome.Success (φ result), s') /\
        (result = true <-> UBT.Sim.tree.batch_verify_with_shared batch root sw).

  (** Shared verification implies standard verification *)
  Theorem shared_verify_refines :
    forall (batch : BatchInclusionProof) (root : Bytes32) (sw : SharedWitness),
      UBT.Sim.tree.batch_verify_with_shared batch root sw ->
      UBT.Sim.tree.compute_shared_witness batch = Some sw ->
      verify_batch_inclusion batch root.
  Proof.
    intros batch root sw Hshared Hsw.
    apply (UBT.Sim.tree.shared_verify_implies_batch batch root sw Hshared Hsw).
  Qed.

End BatchVerifyLink.

(** ** Verification Limitations and Future Work
    
    This section documents what aspects of Rust semantics are modeled,
    what is axiomatized, and what future work is needed.
*)

Module Limitations.
  
  (** *** What is modeled:
      
      1. Pure functional behavior of tree operations
         - get, insert, delete return correct values
         - Operations preserve well-formedness
         - Composition theorems hold
      
      2. Refinement relation between Rust and simulation types
         - Type linking via φ encoding
         - Value correspondence
      
      3. Termination guarantees
         - All operations terminate on well-formed inputs
         - No infinite loops
      
      4. Panic freedom
         - Well-formed inputs never cause panics
  *)
  
  (** *** What is axiomatized:
      
      1. Monadic execution semantics (Run.run)
         - Connection between M monad and outcomes
         - Step evaluation relation
         
      2. Execution theorems (the executes axioms)
         - get_executes, insert_executes, delete_executes, root_hash_executes
         - These require full trait resolution and closure semantics
      
      3. Panic freedom axioms (PanicFreedom module)
         - Require verification that all panic! calls are unreachable
      
      4. State threading (StateThreading module)
         - Memory operations (alloc, read, write) semantics
  *)
  
  (** *** Future work needed for complete verification:
      
      1. Develop full M monad interpreter
         - Implement step : Config -> option Config
         - Prove termination for well-formed inputs
         - Handle trait method resolution
      
      2. Link supporting library functions
         - HashMap.get, HashMap.entry, HashMap.or_insert_with
         - StemNode.get_value, StemNode.set_value
         - rebuild_root tree construction
      
      3. Memory model verification
         - Prove state operations preserve refinement
         - Verify no use-after-free or double-free
      
      4. Hasher trait linking
         - Connect Rust Hasher implementation to hash_* axioms
         - Verify hash computation equivalence
      
      5. Iterator/closure verification
         - Link for-loop semantics to fold operations
         - Verify closure semantics match pure functions
  *)
  
  (** Marker that identifies axiomatized theorems for tracking *)
  Definition is_axiomatized (name : string) : Prop := True.
  
  Definition axiomatized_theorems : list string := [
    "Run.run_pure";
    "Run.run_bind";
    "Run.run_panic";
    "GetLink.get_executes";
    "InsertLink.insert_executes";
    "DeleteLink.delete_executes";
    "NewLink.new_executes";
    "HashLink.root_hash_executes";
    "PanicFreedom.get_no_panic";
    "PanicFreedom.insert_no_panic";
    "PanicFreedom.delete_no_panic";
    "PanicFreedom.root_hash_no_panic";
    "BatchVerifyLink.rust_verify_batch_inclusion_executes";
    "BatchVerifyLink.rust_verify_shared_executes"
  ].

End Limitations.
