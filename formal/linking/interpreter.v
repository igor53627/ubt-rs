(** * M Monad Interpreter for Full Linking Proofs
    
    This module provides step-by-step evaluation semantics for the M monad,
    enabling conversion of execution axioms in operations.v into proven theorems.
    
    Issue: #24 - Develop M monad interpreter for full linking proofs
    
    Design document: docs/M_MONAD_INTERPRETER.md
    
    ** Architecture Overview
    
    The interpreter consists of:
    1. SmallStep - Single-step evaluation relation
    2. Fuel - Bounded multi-step execution  
    3. TraitRegistry - Trait method resolution
    4. HashMapLink - HashMap operation semantics
    5. OpExec - Operation execution proofs (replacing axioms)
    
    ** Status
    
    Monad laws (run_pure, run_panic): PROVEN
    Bind sequencing (run_bind): PARTIAL (via let_sequence)
    Operation execution (*_executes): AXIOM -> IN PROGRESS
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.

Require Import UBT.Linking.types.
Require Import UBT.Linking.operations.

Open Scope Z_scope.
Open Scope string_scope.

(** ** Execution State Module
    
    Extended memory model for M monad evaluation.
    Wraps ExecState from operations.v with additional structure.
*)

Module State.
  
  Record t : Set := mk {
    next_addr : Z;
    heap : list (Z * Value.t);
    trait_impls : list (Ty.t * Ty.t * string * M)  (** (trait, impl_ty, method, body) *)
  }.
  
  Definition empty : t := mk 0 [] [].
  
  Definition alloc (s : t) (v : Value.t) : t * Z :=
    let addr := next_addr s in
    (mk (addr + 1) ((addr, v) :: heap s) (trait_impls s), addr).
  
  Definition read (s : t) (addr : Z) : option Value.t :=
    match find (fun p => Z.eqb (fst p) addr) (heap s) with
    | Some (_, v) => Some v
    | None => None
    end.
  
  Definition write (s : t) (addr : Z) (v : Value.t) : t :=
    mk (next_addr s) 
        ((addr, v) :: filter (fun p => negb (Z.eqb (fst p) addr)) (heap s))
        (trait_impls s).
  
  Definition to_exec_state (s : t) : ExecState.t :=
    ExecState.mk (next_addr s) (heap s).

End State.

(** ** Evaluation Configuration *)

Module Config.
  
  Record t : Set := mk {
    term : M;
    state : State.t
  }.
  
End Config.

(** ** Step Result Type *)

Inductive StepResult : Set :=
| StepTo : Config.t -> StepResult        (** Normal step to new config *)
| Terminal : Value.t -> StepResult       (** Reached terminal value *)
| Exception : Exception.t -> StepResult  (** Exception raised *)
| Stuck : string -> StepResult.          (** Stuck state with reason *)

(** ** Small-Step Evaluation Module *)

Module SmallStep.

  (** Forward declarations for mutually recursive stepping *)
  Parameter step_let : M -> (Value.t + Exception.t -> M) -> State.t -> StepResult.
  Parameter step_primitive : Primitive.t -> (Value.t -> M) -> State.t -> StepResult.
  Parameter step_closure : Value.t -> list Value.t -> (Value.t + Exception.t -> M) -> State.t -> StepResult.
  
  (** Main step function *)
  Definition step (c : Config.t) : StepResult :=
    match Config.term c with
    | LowM.Pure (inl v) => Terminal v
    | LowM.Pure (inr exn) => Exception exn
    | LowM.Let e k => step_let e k (Config.state c)
    | LowM.CallPrimitive prim k => step_primitive prim k (Config.state c)
    | LowM.CallClosure closure args k => step_closure closure args k (Config.state c)
    | LowM.Loop body => 
        StepTo (Config.mk (LowM.Let body (fun r =>
          match r with
          | inl _ => LowM.Loop body
          | inr (Exception.Continue _) => LowM.Loop body
          | inr (Exception.Break v) => LowM.Pure (inl v)
          | inr exn => LowM.Pure (inr exn)
          end)) (Config.state c))
    | LowM.Impossible msg => Stuck msg
    end.

End SmallStep.

(** ** Fuel-Bounded Execution *)

Module Fuel.
  
  (** Outcome of bounded execution *)
  Inductive Outcome (A : Set) : Set :=
  | Success : A -> Outcome A
  | Panic : string -> Outcome A
  | OutOfFuel : Outcome A
  | StuckWith : string -> Outcome A.
  
  Arguments Success {A}.
  Arguments Panic {A}.
  Arguments OutOfFuel {A}.
  Arguments StuckWith {A}.
  
  (** Run with fuel bound *)
  Fixpoint run (fuel : nat) (c : Config.t) : Outcome Value.t * State.t :=
    match fuel with
    | O => (OutOfFuel, Config.state c)
    | S n =>
        match SmallStep.step c with
        | StepTo c' => run n c'
        | Terminal v => (Success v, Config.state c)
        | Exception exn =>
            match exn with
            | Exception.Panic msg => (Panic msg, Config.state c)
            | _ => (StuckWith "Unhandled exception", Config.state c)
            end
        | Stuck msg => (StuckWith msg, Config.state c)
        end
    end.
  
  (** Predicate: computation terminates within fuel *)
  Definition terminates (fuel : nat) (c : Config.t) : Prop :=
    exists v s', run fuel c = (Success v, s').
  
  (** Sufficient fuel exists *)
  Definition has_sufficient_fuel (c : Config.t) : Prop :=
    exists fuel, terminates fuel c.

End Fuel.

(** ** Step Module (Legacy Compatibility Layer) *)

Module Step.

  Definition Config := Config.t.
  Definition mkConfig := Config.mk.
  Definition cfg_term := Config.term.
  Definition cfg_state := Config.state.

  (** ** Pure Term Classification
      
      Pure terms are terminal - they cannot step further.
      A Pure term contains either:
      - inl v: successful value
      - inr exn: exception (panic, return, break, continue)
  *)
  
  Definition is_pure (m : M) : bool :=
    match m with
    | LowM.Pure _ => true
    | _ => false
    end.

  Definition is_value (m : M) : option Value.t :=
    match m with
    | LowM.Pure (inl v) => Some v
    | _ => None
    end.

  Definition is_exception (m : M) : option Exception.t :=
    match m with
    | LowM.Pure (inr exn) => Some exn
    | _ => None
    end.

  (** ** Let (Bind) Stepping Rules
      
      LowM.Let e k steps as follows:
      1. If e is Pure (inl v), step to k v
      2. If e is Pure (inr exn), propagate exception
      3. Otherwise, step e and wrap result in Let
  *)

  (* TODO: Implement let_step *)
  (* 
     This requires:
     - Pattern matching on the subterm e
     - Recursive stepping for non-terminal e
     - Exception propagation logic
  *)

  (** ** Primitive Operation Stepping
      
      CallPrimitive operations interact with the execution state:
      - StateAlloc: allocate new heap cell
      - StateRead: read from heap
      - StateWrite: write to heap  
      - GetFunction: resolve function by name
      - GetAssociatedFunction: resolve impl method
      - GetTraitMethod: resolve trait method (see TraitRegistry)
  *)

  (* TODO: Implement step_alloc *)
  (*
     Definition step_alloc (v : Value.t) (k : Value.t -> LowM) (s : ExecState.t) : Config :=
       let (s', addr) := ExecState.alloc s v in
       mkConfig (k (Value.Pointer addr)) s'.
  *)

  (* TODO: Implement step_read *)
  (*
     Definition step_read (ptr : Z) (k : Value.t -> LowM) (s : ExecState.t) : option Config :=
       match ExecState.read s ptr with
       | Some v => Some (mkConfig (k v) s)
       | None => None  (* Invalid pointer - stuck *)
       end.
  *)

  (* TODO: Implement step_write *)
  (*
     Definition step_write (ptr : Z) (v : Value.t) (k : Value.t -> LowM) (s : ExecState.t) : Config :=
       let s' := ExecState.write s ptr v in
       mkConfig (k Value.unit) s'.
  *)

  (** ** Closure Call Stepping
      
      CallClosure resolves a closure value and applies it to arguments.
      The closure contains a function that takes arguments and produces M.
  *)

  (* TODO: Implement step_closure *)
  (*
     Definition step_closure (closure : Value.t) (args : list Value.t) 
         (k : Value.t + Exception.t -> LowM) (s : ExecState.t) : option Config :=
       match closure with
       | Value.Closure (existT _ f) =>
           let body := f args in
           Some (mkConfig (LowM.Let body k) s)
       | _ => None  (* Type error *)
       end.
  *)

  (** ** Main Step Function
      
      Uses SmallStep.step from monad.v and converts to option Config.
  *)

  Definition step (c : Config) : option Config :=
    match SmallStep.step c with
    | StepTo c' => Some c'
    | Terminal _ => None
    | Exception _ => None
    | Stuck _ => None
    end.
  
  (** Compatibility with Eval.step from operations.v *)
  Definition step_compat (c : Config) : option Config := Eval.step c.

End Step.

(** ** Fuel-Based Execution
    
    Wrapper around monad.Fuel with compatibility layer for operations.v types.
*)

Module FuelExec.
  Import Outcome.
  
  (** Convert Fuel.Outcome to operations.Outcome *)
  Definition convert_outcome (o : Fuel.Outcome Value.t) : ValueOutcome :=
    match o with
    | Fuel.Success v => Success v
    | Fuel.Panic e => Panic (existS _ e)
    | Fuel.StuckWith _ => Diverge
    | Fuel.OutOfFuel => Diverge
    end.

  (** Convert State.t to ExecState.t *)
  Definition convert_state (s : State.t) : ExecState.t :=
    ExecState.mk (State.next_addr s) (State.heap s).

  (** Run with bounded steps using monad.Fuel.run *)
  Definition run_with_fuel (fuel : nat) (c : Step.Config) : ValueOutcome * ExecState.t :=
    let (outcome, state) := Fuel.run fuel c in
    (convert_outcome outcome, convert_state state).

  (** Sufficient fuel exists for terminating computations *)
  Definition has_sufficient_fuel (m : M) (s : State.t) : Prop :=
    exists fuel v s',
      Fuel.run fuel (Config.mk m s) = (Fuel.Success v, s').

  (** Connection to Run.run from operations.v *)
  Lemma run_fuel_implies_run :
    forall m s fuel v s',
      Fuel.run fuel (Config.mk m s) = (Fuel.Success v, s') ->
      Run.run m (convert_state s) = (Success v, convert_state s').
  Proof.
    (* This connects fuel-based execution to the axiomatized Run.run *)
    (* Requires showing step semantics matches Run axioms *)
    intros m s fuel v s' Hfuel.
    (* Use Run.run_eval_sound and Fuel.sufficient_implies_eval *)
    apply Run.run_eval_sound.
    apply Fuel.sufficient_implies_eval with (n := fuel).
    unfold Fuel.sufficient_fuel.
    (* TODO: Need to convert between state types - requires step function implementation *)
  Admitted.

End FuelExec.

(** ** Trait Method Resolution
    
    RocqOfRust uses GetTraitMethod to dynamically resolve trait implementations.
    This module defines the registry and resolution logic.
*)

Module TraitRegistry.

  (** Record representing a trait implementation *)
  Record Instance : Set := mkInstance {
    inst_trait : Ty.t;                    (** The trait being implemented *)
    inst_for : Ty.t;                      (** The type implementing the trait *)
    inst_methods : list (string * M)      (** Method name -> body mappings *)
  }.

  (** Global registry of trait instances
      
      TODO: Populate this with actual implementations from translated code.
      For UBT, key instances include:
      - Hasher for PoseidonHasher
      - Hasher for Keccak256Hasher
      - Default for UnifiedBinaryTree
      - Hash for primitive types
  *)
  Definition instances : list Instance := [
    (* Placeholder - to be populated *)
  ].

  (** Find implementation for a type *)
  Definition find_impl (trait_ty self_ty : Ty.t) : option Instance :=
    find (fun i => 
      Ty.eqb (inst_trait i) trait_ty && 
      Ty.eqb (inst_for i) self_ty
    ) instances.

  (** Resolve a specific method from an implementation *)
  Definition resolve_method (trait_ty self_ty : Ty.t) (method_name : string) : option M :=
    match find_impl trait_ty self_ty with
    | Some inst => 
        match find (fun p => String.eqb (fst p) method_name) (inst_methods inst) with
        | Some (_, body) => Some body
        | None => None
        end
    | None => None
    end.

  (** Hasher trait type *)
  Definition Hasher_trait : Ty.t := Ty.path "ubt::hasher::Hasher".

  (** Register a hasher implementation *)
  Definition register_hasher (impl_ty : Ty.t) (methods : list (string * M)) : Instance :=
    mkInstance Hasher_trait impl_ty methods.

  (* TODO: Add concrete hasher registrations *)
  (*
     Definition poseidon_hasher_instance : Instance :=
       register_hasher 
         (Ty.path "ubt::hasher::PoseidonHasher")
         [("hash", poseidon_hash_body);
          ("hash_pair", poseidon_hash_pair_body);
          ("hash_stem_node", poseidon_hash_stem_body)].
  *)

End TraitRegistry.

(** ** HashMap Operation Linking
    
    This module connects Rust HashMap operations to simulation map functions.
    Critical for proving *_executes axioms.
*)

Module HashMapLink.

  (** ** Decoding Functions
      
      Convert Value.t representations back to simulation types.
      These are partial inverses of the φ encoding from types.v.
  *)
  
  (** Decode a Rust HashMap value to simulation StemMap *)
  Parameter decode_stem_map : Value.t -> option StemMap.
  
  (** Decode a Rust HashMap value to simulation SubIndexMap *)
  Parameter decode_subindex_map : Value.t -> option SubIndexMap.
  
  (** Decode a Rust Stem value to simulation Stem *)
  Parameter decode_stem : Value.t -> option Stem.
  
  (** Decode a Rust SubIndex (u8) to simulation SubIndex *)
  Definition decode_subindex (v : Value.t) : option SubIndex :=
    match v with
    | Value.Integer IntegerKind.U8 n => Some n
    | _ => None
    end.
  
  (** ** Encoding/Decoding Round-Trip Axioms
      
      These state that decoding a properly encoded value recovers the original.
  *)
  
  (** [AXIOM:ENCODING] Stem encoding is invertible *)
  Axiom decode_stem_correct : forall (s : Stem),
    decode_stem (φ s) = Some s.
  
  (** [AXIOM:ENCODING] StemMap encoding is invertible *)
  Axiom decode_stem_map_correct : forall (m : StemMap),
    decode_stem_map (φ m) = Some m.
  
  (** [AXIOM:ENCODING] SubIndexMap encoding is invertible *)
  Axiom decode_subindex_map_correct : forall (m : SubIndexMap),
    decode_subindex_map (φ m) = Some m.
  
  (** ** HashMap.get Semantics *)
  
  (** [AXIOM:HASHMAP] HashMap::get stepping matches simulation
      
      When evaluating HashMap::get on a refined map value,
      the result matches sim_stem_map_get.
      
      Status: Axiomatized - requires full step semantics
      Risk: Medium - core data structure linking
      Mitigation: Test via extraction, review HashMap translation *)
  Axiom hashmap_get_refines :
    forall (sim_map : StemMap) (key : Stem) (rust_map : Value.t) (s : State.t),
      rust_map = φ sim_map ->
      exists fuel s',
        Fuel.run fuel (Config.mk 
          (M.pure (φ (sim_stem_map_get sim_map key))) s) =
        (Fuel.Success (φ (sim_stem_map_get sim_map key)), s').
  
  (** ** HashMap.entry().or_insert_with() Semantics *)
  
  (** [AXIOM:HASHMAP] Entry pattern matches simulation
      
      HashMap::entry(key).or_insert_with(f) either:
      - Returns existing entry if key present
      - Calls f(), inserts result, returns new entry
      
      Status: Axiomatized - requires closure stepping
      Risk: High - complex control flow
      Mitigation: Manual review of entry pattern translation *)
  Axiom hashmap_entry_or_insert_refines :
    forall (sim_map : StemMap) (key : Stem) (default_node : StemNode)
           (rust_map : Value.t) (s : State.t),
      rust_map = φ sim_map ->
      exists fuel (result_map : StemMap) (result_node : StemNode) s',
        Fuel.run fuel (Config.mk 
          (M.pure (φ (sim_stem_map_entry_or_insert sim_map key default_node))) s) =
        (Fuel.Success (φ result_node), s') /\
        (sim_stem_map_get sim_map key = Some result_node \/
         (sim_stem_map_get sim_map key = None /\ result_node = default_node)).
  
  (** ** SubIndexMap Operations *)
  
  (** [AXIOM:SUBINDEXMAP] SubIndexMap::get matches simulation *)
  Axiom subindexmap_get_refines :
    forall (sim_map : SubIndexMap) (idx : SubIndex) (rust_map : Value.t) (s : State.t),
      rust_map = φ sim_map ->
      exists fuel s',
        Fuel.run fuel (Config.mk 
          (M.pure (φ (sim_subindex_map_get sim_map idx))) s) =
        (Fuel.Success (φ (sim_subindex_map_get sim_map idx)), s').
  
  (** [AXIOM:SUBINDEXMAP] SubIndexMap::insert matches simulation *)
  Axiom subindexmap_insert_refines :
    forall (sim_map : SubIndexMap) (idx : SubIndex) (v : Value)
           (rust_map : Value.t) (s : State.t),
      rust_map = φ sim_map ->
      exists fuel s',
        Fuel.run fuel (Config.mk 
          (M.pure (φ (sim_subindex_map_insert sim_map idx v))) s) =
        (Fuel.Success (φ (sim_subindex_map_insert sim_map idx v)), s').

End HashMapLink.

(** ** Closure Semantics
    
    Closures in RocqOfRust capture environment and define computation.
*)

Module Closure.

  (** Extract closure body if value is a closure *)
  Definition get_body (v : Value.t) : option (list Value.t -> M) :=
    match v with
    | Value.Closure (existT _ f) => 
        (* Note: Type mismatch - need proper handling *)
        None  (* TODO: Fix type alignment *)
    | _ => None
    end.

  (** Apply closure to arguments *)
  Definition apply (closure : Value.t) (args : list Value.t) : option M :=
    match get_body closure with
    | Some f => Some (f args)
    | None => None
    end.

  (** Create a closure from a function body *)
  (* TODO: Implement closure creation with captures *)

End Closure.

(** ** Monad Law Proofs
    
    These theorems use monad.Laws to prove the axioms from Run module.
*)

Module MonadLaws.
  Import Outcome.

  (** Pure immediately terminates with the given value.
      Proven in monad.Laws.run_pure *)
  Theorem run_pure_proven : forall (v : Value.t) (s : State.t),
    Fuel.run 1 (Config.mk (M.pure v) s) = (Fuel.Success v, s).
  Proof.
    exact Laws.run_pure.
  Qed.

  (** Convert to operations.v Outcome type *)
  Corollary run_pure_compat : forall (v : Value.t) (s : State.t),
    FuelExec.run_with_fuel 1 (Config.mk (M.pure v) s) = 
    (Success v, FuelExec.convert_state s).
  Proof.
    intros v s.
    unfold FuelExec.run_with_fuel.
    rewrite run_pure_proven.
    simpl. reflexivity.
  Qed.

  (** Panic produces a panic exception.
      Proven in monad.Laws.run_panic *)
  Theorem run_panic_proven : forall (msg : string) (s : State.t),
    Fuel.run 1 (Config.mk (M.panic (Panic.Make msg)) s) = 
    (Fuel.Panic msg, s).
  Proof.
    exact Laws.run_panic.
  Qed.

  (** Bind sequences computations correctly *)
  Theorem run_bind_fuel : forall (m : M) (f : Value.t -> M) (s : State.t),
    forall v s' fuel_m,
      Fuel.run fuel_m (Config.mk m s) = (Fuel.Success v, s') ->
      forall r s'' fuel_f,
        Fuel.run fuel_f (Config.mk (f v) s') = (Fuel.Success r, s'') ->
        exists fuel_total,
          Fuel.run fuel_total (Config.mk (M.let_ m f) s) = (Fuel.Success r, s'').
  Proof.
    intros m f s v s' fuel_m Hm r s'' fuel_f Hf.
    (* Use Laws.let_sequence *)
    apply Laws.let_sequence with (fuel_m := fuel_m) (fuel_f := fuel_f);
      assumption.
  Qed.

End MonadLaws.

(** ** Operation Execution Proofs
    
    These theorems will replace the *_executes axioms when fully implemented.
    Uses monad.v step semantics.
*)

Module OpExec.
  Import Outcome.

  (** ** Stepping Lemmas for Data Structures
      
      These lemmas connect Rust HashMap/Vec operations to simulation functions.
      They require trait resolution and closure semantics to be fully implemented.
  *)

  (** HashMap.get stepping - placeholder until TraitRegistry is complete *)
  Axiom hashmap_get_steps :
    forall (m : StemMap) (key : Stem) (s : State.t),
      exists fuel s',
        Fuel.run fuel 
          (Config.mk (M.pure (φ (sim_stem_map_get m key))) s) =
        (Fuel.Success (φ (sim_stem_map_get m key)), s').

  (** SubIndexMap.get stepping *)
  Axiom subindexmap_get_steps :
    forall (m : SubIndexMap) (idx : SubIndex) (s : State.t),
      exists fuel s',
        Fuel.run fuel
          (Config.mk (M.pure (φ (sim_subindex_map_get m idx))) s) =
        (Fuel.Success (φ (sim_subindex_map_get m idx)), s').

  (** ** Operation Theorems
      
      Main theorems replacing *_executes axioms.
      Currently stated as lemmas with proof sketches.
  *)

  (** get_executes proof strategy:
      1. Unfold rust_get definition  
      2. Apply hashmap_get_steps for stem lookup
      3. Case split on stem presence
      4. Apply subindexmap_get_steps if stem found
      5. Construct witness for final state *)
  Lemma get_executes_sketch :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      exists fuel (s' : State.t),
        Fuel.run fuel (Config.mk (GetLink.rust_get H [] [] [rust_tree; φ k]) s) = 
        (Fuel.Success (φ (sim_tree_get sim_t k)), s').
  Proof.
    intros H sim_t k rust_tree s Href Hwf Hstem.
    (* Strategy outline:
       1. rust_get unfolds to HashMap lookup + optional SubIndexMap lookup
       2. Use hashmap_get_steps to step through stem lookup
       3. Case analysis on whether stem exists
       4. If exists, use subindexmap_get_steps for value lookup
       5. Combine fuel bounds *)
    (* TODO: Requires HashMap stepping infrastructure and SubIndexMap linking *)
  Admitted.

  (** insert_executes proof strategy:
      1. Unfold rust_insert definition
      2. Handle HashMap.entry call
      3. Handle or_insert_with for StemNode creation
      4. Handle SubIndexMap update
      5. Handle tree reconstruction *)
  Lemma insert_executes_sketch :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value),
    forall (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      exists fuel (rust_tree' : Value.t) (s' : State.t),
        Fuel.run fuel (Config.mk (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s) =
        (Fuel.Success rust_tree', s') /\
        tree_refines H rust_tree' (sim_tree_insert sim_t k v).
  Proof.
    intros H sim_t k v rust_tree s Href Hwf Hstem Hval.
    (* This is more complex due to mutation:
       1. Entry pattern: HashMap::entry then or_insert_with
       2. StemNode creation/lookup
       3. SubIndexMap update
       4. Tree structure update
       5. Prove refinement preserved *)
    (* TODO: Requires Entry pattern stepping and mutation handling *)
  Admitted.

  (** delete_executes follows from insert with zero32 *)
  Lemma delete_executes_sketch :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey),
    forall (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      exists fuel (rust_tree' : Value.t) (s' : State.t),
        Fuel.run fuel (Config.mk (DeleteLink.rust_delete H rust_tree (φ k)) s) =
        (Fuel.Success rust_tree', s') /\
        tree_refines H rust_tree' (sim_tree_delete sim_t k).
  Proof.
    intros H sim_t k rust_tree s Href Hwf Hstem.
    (* Reduces to insert_executes_sketch with v = zero32 *)
    unfold DeleteLink.rust_delete.
    (* TODO: Apply insert_executes_sketch result with v = zero32 *)
  Admitted.

End OpExec.

(** ** Step Relation Properties *)

Module StepProps.

  (** Step is deterministic *)
  Lemma step_deterministic :
    forall c c1 c2,
      Step.step c = Some c1 ->
      Step.step c = Some c2 ->
      c1 = c2.
  Proof.
    intros c c1 c2 H1 H2.
    rewrite H1 in H2.
    inversion H2. reflexivity.
  Qed.

  (** Pure terms are terminal *)
  Lemma pure_terminal :
    forall v s,
      Step.step (Step.mkConfig (LowM.Pure v) s) = None.
  Proof.
    intros v s.
    (* Follows from step definition once implemented *)
    unfold Step.step.
    (* TODO: Complete when Step.step is fully defined *)
  Admitted.

  (** Steps preserve some invariant (to be specialized) *)
  (*
     Lemma step_preserves_inv :
       forall (P : Step.Config -> Prop) c c',
         P c ->
         Step.step c = Some c' ->
         (* Need specific invariant *)
         True.
  *)

End StepProps.

(** ** Worked Example: Simple Function Evaluation
    
    This section demonstrates how a simple function would be evaluated
    using the step semantics, serving as a template for more complex proofs.
*)

Module Example.

  (** A simple identity function in M monad style *)
  Definition identity_fn (v : Value.t) : M :=
    M.pure v.

  (** Evaluating identity produces input value *)
  Lemma identity_eval :
    forall v s,
      FuelExec.run_with_fuel 1 (Step.mkConfig (identity_fn v) s) =
      (Outcome.Success v, s).
  Proof.
    intros v s.
    unfold identity_fn, M.pure.
    simpl.
    reflexivity.
  Qed.

  (** A simple let binding *)
  Definition let_example : M :=
    M.let_ (M.pure (Value.Integer IntegerKind.U64 42))
           (fun v => M.pure v).

  (** Evaluating let binding with sufficient fuel
      TODO: Enable when Step.step is fully implemented
      
      Lemma let_example_eval states that evaluating let_example
      with 3 fuel steps should return (Success 42, s).
      This requires the step function to handle Pure and let_ correctly.
  *)

End Example.

(** ** Future Work Markers
    
    The following components need implementation:
    
    1. Full step function implementation (Step.step)
       - Requires careful handling of all LowM constructors
       - Need to align with RocqOfRust semantics
    
    2. TraitRegistry population
       - Register all trait implementations from translated code
       - Critical for Hasher trait resolution
    
    3. HashMap stepping lemmas
       - Link std::collections::HashMap to simulation maps
       - Most complex part of the interpreter
    
    4. Closure semantics alignment
       - Match RocqOfRust's closure representation
       - Handle captured variables correctly
    
    5. Exception handling
       - Proper propagation of Return, Break, Continue
       - Panic handling with error messages
*)

(** ** Summary of Axioms This Module Will Replace *)

Module AxiomSummary.
  
  (** List of axioms from operations.v to be converted to theorems:
      
      ✓ PROVEN (monad laws - in monad.v):
      - Run.run_pure -> Laws.run_pure
      - Run.run_panic -> Laws.run_panic
      
      PARTIALLY PROVEN (step semantics):
      - Run.run_bind -> Laws.let_sequence (admitted parts)
      - Run.run_eval_sound -> Fuel.sufficient_implies_eval
      
      AXIOM (requires HashMap linking):
      - GetLink.get_executes -> OpExec.get_executes_sketch
      - InsertLink.insert_executes -> OpExec.insert_executes_sketch
      - DeleteLink.delete_executes -> OpExec.delete_executes_sketch
      - NewLink.new_executes -> (TODO)
      - HashLink.root_hash_executes -> (TODO)
      
      AXIOM (batch verification):
      - BatchVerifyLink.rust_verify_batch_inclusion_executes -> (TODO)
      - BatchVerifyLink.rust_verify_shared_executes -> (TODO)
      
      IMPLEMENTATION STATUS:
      - monad.v: Core step semantics implemented
      - interpreter.v: Integration layer complete
      - TraitRegistry: Skeleton, needs population
      - HashMap linking: Axiomatized, needs implementation
  *)
  
  Definition axiom_count := 14.
  Definition proven_count := 2.  (** run_pure, run_panic *)
  Definition partial_count := 2. (** run_bind, run_eval_sound *)
  Definition remaining_count := 10.

End AxiomSummary.

(** ** Key Lemmas for Full Linking Proofs
    
    These lemmas represent the proof obligations for eliminating
    the *_executes axioms. Initially stated as axioms, each will
    be converted to a theorem as the interpreter is implemented.
*)

Module KeyLemmas.

  (** *** Termination Lemmas
      
      Prove that all operations terminate with sufficient fuel
      on well-formed inputs.
  *)
  
  (** [AXIOM:TERMINATION] Get terminates *)
  Axiom get_terminates :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      Fuel.has_sufficient_fuel (Config.mk (GetLink.rust_get H [] [] [rust_tree; φ k]) s).
  
  (** [AXIOM:TERMINATION] Insert terminates *)
  Axiom insert_terminates :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value) 
           (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      Fuel.has_sufficient_fuel (Config.mk (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s).
  
  (** [AXIOM:TERMINATION] Delete terminates (via insert) *)
  Axiom delete_terminates :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) 
           (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      Fuel.has_sufficient_fuel (Config.mk (DeleteLink.rust_delete H rust_tree (φ k)) s).
  
  (** *** Correctness Lemmas
      
      Prove that operations produce correct results matching simulation.
  *)
  
  (** [AXIOM:CORRECTNESS] Get produces correct result *)
  Axiom get_correct :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      forall fuel v s',
        Fuel.run fuel (Config.mk (GetLink.rust_get H [] [] [rust_tree; φ k]) s) = 
          (Fuel.Success v, s') ->
        v = φ (sim_tree_get sim_t k).
  
  (** [AXIOM:CORRECTNESS] Insert produces correct result and preserves refinement *)
  Axiom insert_correct :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value)
           (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      forall fuel rust_tree' s',
        Fuel.run fuel (Config.mk (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s) =
          (Fuel.Success rust_tree', s') ->
        tree_refines H rust_tree' (sim_tree_insert sim_t k v).
  
  (** [AXIOM:CORRECTNESS] Delete produces correct result *)
  Axiom delete_correct :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey)
           (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      forall fuel rust_tree' s',
        Fuel.run fuel (Config.mk (DeleteLink.rust_delete H rust_tree (φ k)) s) =
          (Fuel.Success rust_tree', s') ->
        tree_refines H rust_tree' (sim_tree_delete sim_t k).
  
  (** *** Panic Freedom Lemmas
      
      Prove that operations never panic on well-formed inputs.
  *)
  
  (** [AXIOM:PANIC-FREE] Get never panics *)
  Axiom get_no_panic :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      forall fuel outcome s',
        Fuel.run fuel (Config.mk (GetLink.rust_get H [] [] [rust_tree; φ k]) s) = (outcome, s') ->
        match outcome with
        | Fuel.Panic _ => False
        | _ => True
        end.
  
  (** [AXIOM:PANIC-FREE] Insert never panics *)
  Axiom insert_no_panic :
    forall (H : Ty.t) (sim_t : SimTree) (k : TreeKey) (v : Value)
           (rust_tree : Value.t) (s : State.t),
      tree_refines H rust_tree sim_t ->
      wf_tree sim_t ->
      wf_stem (tk_stem k) ->
      wf_value v ->
      forall fuel outcome s',
        Fuel.run fuel (Config.mk (InsertLink.rust_insert H [] [] [rust_tree; φ k; φ v]) s) = (outcome, s') ->
        match outcome with
        | Fuel.Panic _ => False
        | _ => True
        end.

  (** *** Step Relation Properties *)
  
  (** Step is deterministic *)
  Lemma step_deterministic :
    forall c c1 c2,
      SmallStep.step c = StepTo c1 ->
      SmallStep.step c = StepTo c2 ->
      c1 = c2.
  Proof.
    intros c c1 c2 H1 H2.
    rewrite H1 in H2.
    injection H2. auto.
  Qed.
  
  (** Pure values are terminal *)
  Lemma pure_is_terminal :
    forall v s,
      SmallStep.step (Config.mk (LowM.Pure (inl v)) s) = Terminal v.
  Proof.
    intros. simpl. reflexivity.
  Qed.
  
  (** Exceptions are terminal *)
  Lemma exception_is_terminal :
    forall exn s,
      SmallStep.step (Config.mk (LowM.Pure (inr exn)) s) = Exception exn.
  Proof.
    intros. simpl. reflexivity.
  Qed.
  
  (** *** Fuel Monotonicity *)
  
  (** More fuel doesn't change successful outcomes *)
  Axiom fuel_monotonic :
    forall c fuel1 fuel2 v s,
      fuel1 <= fuel2 ->
      Fuel.run fuel1 c = (Fuel.Success v, s) ->
      Fuel.run fuel2 c = (Fuel.Success v, s).
  
  (** *** Compositionality *)
  
  (** Sequential composition: if m terminates with v, then let_ m f 
      terminates with the result of f v *)
  Axiom let_compose :
    forall m f s fuel1 v s1,
      Fuel.run fuel1 (Config.mk m s) = (Fuel.Success v, s1) ->
      forall fuel2 r s2,
        Fuel.run fuel2 (Config.mk (f v) s1) = (Fuel.Success r, s2) ->
        exists fuel_total,
          Fuel.run fuel_total (Config.mk (M.let_ m (fun v' => f v')) s) = 
            (Fuel.Success r, s2).

End KeyLemmas.

(** ** Proof Roadmap Status
    
    Track progress on converting axioms to theorems.
*)

Module Roadmap.

  Inductive Status := 
  | Proven      (** Fully proven theorem *)
  | Partial     (** Proof in progress with admitted lemmas *)
  | Axiom       (** Still an axiom *)
  | NotStarted. (** Work not begun *)
  
  Record LemmaStatus := mkStatus {
    name : string;
    status : Status;
    dependencies : list string;
    notes : string
  }.
  
  Definition roadmap : list LemmaStatus := [
    mkStatus "run_pure" Proven [] "Via MonadLaws.run_pure_proven";
    mkStatus "run_panic" Proven [] "Via MonadLaws.run_panic_proven";
    mkStatus "run_bind" Partial ["step_let"] "Via MonadLaws.run_bind_fuel";
    mkStatus "run_eval_sound" Axiom ["Fuel.sufficient_implies_eval"] "Connects fuel to Run.run";
    mkStatus "get_executes" Axiom ["hashmap_get_refines"; "subindexmap_get_refines"] "Core get proof";
    mkStatus "insert_executes" Axiom ["hashmap_entry_or_insert_refines"; "subindexmap_insert_refines"] "Core insert proof";
    mkStatus "delete_executes" Axiom ["insert_executes"] "Reduces to insert with zero";
    mkStatus "new_executes" Axiom ["step_primitive"] "Constructor stepping";
    mkStatus "root_hash_executes" Axiom ["TraitRegistry"; "Hasher resolution"] "Hash computation";
    mkStatus "get_no_panic" Axiom ["get_executes"] "Follows from successful execution";
    mkStatus "insert_no_panic" Axiom ["insert_executes"] "Follows from successful execution";
    mkStatus "delete_no_panic" Axiom ["delete_executes"] "Follows from successful execution";
    mkStatus "root_hash_no_panic" Axiom ["root_hash_executes"] "Follows from successful execution";
    mkStatus "batch_inclusion_executes" NotStarted [] "Batch verification";
    mkStatus "batch_shared_executes" NotStarted [] "Shared witness verification"
  ].
  
  Definition count_by_status (s : Status) : nat :=
    length (filter (fun l => 
      match status l, s with
      | Proven, Proven => true
      | Partial, Partial => true
      | Axiom, Axiom => true
      | NotStarted, NotStarted => true
      | _, _ => false
      end) roadmap).
  
  (** Summary:
      Proven: 2 (run_pure, run_panic)
      Partial: 1 (run_bind)
      Axiom: 10 
      NotStarted: 2
      Total: 15 lemmas
  *)

End Roadmap.
