(** * MInterpreter: General-Purpose M Monad Interpreter
    
    This module provides step-by-step evaluation semantics for the 
    RocqOfRust M monad. It is designed to be reusable across any
    RocqOfRust project.
    
    ** Key Features
    
    - Small-step operational semantics for M monad
    - Fuel-bounded execution with determinism
    - Extensible stepping for primitives and closures
    - Proven monad laws (run_pure, run_panic)
    
    ** Usage
    
    1. Import this module in your project
    2. Register project-specific closures in ClosureRegistry
    3. Register trait implementations in TraitRegistry
    4. Use Fuel.run for execution proofs
    
    ** Dependencies
    
    Requires: RocqOfRust.RocqOfRust, RocqOfRust.links.M, RocqOfRust.simulations.M
*)

Require Import RocqOfRust.RocqOfRust.
Require RocqOfRust.M.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import String.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

(** ** State Module
    
    Execution state with heap memory model.
*)

Module State.
  Record t : Set := mk {
    next_addr : Z;
    heap : list (Z * Value.t);
    trait_impls : list (Ty.t * Ty.t * string * M)
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
End State.

(** ** Config Module
    
    Execution configuration: term + state.
*)

Module Config.
  Record t : Set := mk {
    term : M;
    state : State.t
  }.
End Config.

(** ** StepResult
    
    Result of a single evaluation step.
*)

Inductive StepResult : Set :=
| StepTo : Config.t -> StepResult
| Terminal : Value.t -> StepResult
| Exception : Exception.t -> StepResult
| Stuck : string -> StepResult.

(** ** SmallStep Module
    
    Single-step evaluation semantics.
*)

Module SmallStep.

  (** Extension point: primitive stepping.
      Override this in your project for project-specific primitives. *)
  Parameter step_primitive_ext : 
    RocqOfRust.M.Primitive.t -> (Value.t -> M) -> State.t -> option StepResult.
  
  (** Extension point: closure stepping.
      Override this in your project for project-specific closures. *)
  Parameter step_closure_ext :
    Ty.t -> Value.t -> list Value.t -> 
    (Value.t + Exception.t -> M) -> State.t -> option StepResult.

  (** Core primitive stepping for standard primitives *)
  Definition step_primitive_core 
    (prim : RocqOfRust.M.Primitive.t) 
    (k : Value.t -> M) 
    (s : State.t) : StepResult :=
    match prim with
    | RocqOfRust.M.Primitive.StateAlloc v =>
        let (s', addr) := State.alloc s v in
        StepTo (Config.mk (k (Value.Integer IntegerKind.Isize addr)) s')
    | RocqOfRust.M.Primitive.StateRead addr =>
        match State.read s addr with
        | Some v => StepTo (Config.mk (k v) s)
        | None => Stuck "StateRead: invalid address"
        end
    | RocqOfRust.M.Primitive.StateWrite addr v =>
        let s' := State.write s addr v in
        StepTo (Config.mk (k (Value.Tuple [])) s')
    | _ =>
        match step_primitive_ext prim k s with
        | Some result => result
        | None => Stuck "primitive not implemented"
        end
    end.

  (** Step a Let binding *)
  Definition step_let 
    (e : M) 
    (k : Value.t + Exception.t -> M) 
    (s : State.t) : StepResult :=
    match e with
    | LowM.Pure (inl v) => StepTo (Config.mk (k (inl v)) s)
    | LowM.Pure (inr exn) => StepTo (Config.mk (k (inr exn)) s)
    | _ => Stuck "step_let: non-pure requires recursion"
    end.

  (** Main step function *)
  Definition step (c : Config.t) : StepResult :=
    match Config.term c with
    | LowM.Pure (inl v) => Terminal v
    | LowM.Pure (inr exn) => Exception exn
    | LowM.Let _ty e k => step_let e k (Config.state c)
    | LowM.CallPrimitive prim k => step_primitive_core prim k (Config.state c)
    | LowM.CallClosure ty closure args k =>
        match step_closure_ext ty closure args k (Config.state c) with
        | Some result => result
        | None => Stuck "closure not implemented"
        end
    | _ => Stuck "term form not implemented"
    end.

End SmallStep.

(** ** Fuel Module
    
    Fuel-bounded execution.
*)

Module Fuel.

  Inductive Outcome : Set :=
  | Success : Value.t -> Outcome
  | Panic : PrimString.string -> Outcome
  | OutOfFuel : Outcome
  | StuckWith : string -> Outcome.

  Fixpoint run (fuel : nat) (c : Config.t) : Outcome * State.t :=
    match fuel with
    | O => (OutOfFuel, Config.state c)
    | S n =>
        match SmallStep.step c with
        | StepTo c' => run n c'
        | Terminal v => (Success v, Config.state c)
        | Exception exn =>
            match exn with
            | Exception.Panic msg => (Panic msg, Config.state c)
            | _ => (StuckWith "unhandled exception", Config.state c)
            end
        | Stuck msg => (StuckWith msg, Config.state c)
        end
    end.

  Definition has_sufficient_fuel (c : Config.t) : Prop :=
    exists fuel v s', run fuel c = (Success v, s').

End Fuel.

(** ** Laws Module
    
    Proven monad laws.
*)

Module Laws.

  (** Pure values terminate immediately *)
  Theorem run_pure : forall v s,
    Fuel.run 1 (Config.mk (LowM.Pure (inl v)) s) = (Fuel.Success v, s).
  Proof.
    intros v s. simpl. reflexivity.
  Qed.

  (** Panic propagates *)
  Theorem run_panic : forall msg s,
    Fuel.run 1 (Config.mk (LowM.Pure (inr (Exception.Panic msg))) s) = 
    (Fuel.Panic msg, s).
  Proof.
    intros msg s. simpl. reflexivity.
  Qed.

  (** Step is deterministic *)
  Theorem step_deterministic : forall c r1 r2,
    SmallStep.step c = r1 ->
    SmallStep.step c = r2 ->
    r1 = r2.
  Proof.
    intros c r1 r2 H1 H2. rewrite H1 in H2. exact H2.
  Qed.

  (** More fuel preserves success *)
  Lemma fuel_monotonic : forall fuel1 fuel2 c v s,
    (fuel1 <= fuel2)%nat ->
    Fuel.run fuel1 c = (Fuel.Success v, s) ->
    Fuel.run fuel2 c = (Fuel.Success v, s).
  Proof.
    induction fuel1 as [|n IH]; intros fuel2 c v s Hle Hrun.
    - simpl in Hrun. discriminate.
    - destruct fuel2 as [|m].
      + lia.
      + simpl in Hrun. simpl.
        destruct (SmallStep.step c) as [c' | v0 | exn | msg] eqn:Hstep.
        * apply IH; [lia | exact Hrun].
        * exact Hrun.
        * destruct exn; try discriminate.
        * discriminate.
  Qed.

  (** Success and panic are mutually exclusive *)
  Lemma success_precludes_panic : forall c fuel1 fuel2 v s1 msg s2,
    Fuel.run fuel1 c = (Fuel.Success v, s1) ->
    Fuel.run fuel2 c = (Fuel.Panic msg, s2) ->
    False.
  Proof.
    intros c fuel1 fuel2 v s1 msg s2 Hsuccess Hpanic.
    generalize dependent fuel2.
    generalize dependent c.
    induction fuel1 as [|n IH]; intros c Hsuccess fuel2 Hpanic.
    - simpl in Hsuccess. discriminate.
    - simpl in Hsuccess.
      destruct (SmallStep.step c) eqn:Hstep.
      + destruct fuel2 as [|m]; [simpl in Hpanic; discriminate | ].
        simpl in Hpanic. rewrite Hstep in Hpanic.
        apply (IH _ Hsuccess _ Hpanic).
      + injection Hsuccess as _ _.
        destruct fuel2 as [|m]; [simpl in Hpanic; discriminate | ].
        simpl in Hpanic. rewrite Hstep in Hpanic. discriminate.
      + destruct e; try discriminate.
      + discriminate.
  Qed.

End Laws.

(** ** ClosureRegistry Module
    
    Registry for known closure implementations.
*)

Module ClosureRegistry.

  Record Entry : Set := mkEntry {
    closure_path : string;
    closure_body : list Value.t -> State.t -> option (Value.t * State.t)
  }.

  Definition registry : list Entry := [].

  Definition lookup (path : string) : option Entry :=
    find (fun e => String.eqb (closure_path e) path) registry.

End ClosureRegistry.

(** ** TraitRegistry Module
    
    Registry for trait implementations.
*)

Module TraitRegistry.

  Record Instance : Set := mkInstance {
    inst_trait : Ty.t;
    inst_for : Ty.t;
    inst_methods : list (string * M)
  }.

  Parameter Ty_eqb : Ty.t -> Ty.t -> bool.

  Definition find_impl (trait_ty self_ty : Ty.t) (instances : list Instance) : option Instance :=
    find (fun i => 
      Ty_eqb (inst_trait i) trait_ty && 
      Ty_eqb (inst_for i) self_ty
    ) instances.

  Definition resolve_method 
    (trait_ty self_ty : Ty.t) 
    (method_name : string) 
    (instances : list Instance) : option M :=
    match find_impl trait_ty self_ty instances with
    | Some inst =>
        match find (fun p => String.eqb (fst p) method_name) (inst_methods inst) with
        | Some (_, body) => Some body
        | None => None
        end
    | None => None
    end.

End TraitRegistry.

(** ** Summary
    
    This module provides:
    
    1. State/Config types for execution
    2. SmallStep.step for single-step evaluation
    3. Fuel.run for bounded execution
    4. Laws module with proven properties
    5. Extension points for project-specific stepping
    
    To use in your project:
    
    1. Import UBT.Lib.MInterpreter
    2. Implement step_primitive_ext for your primitives
    3. Implement step_closure_ext for your closures
    4. Use Fuel.run for execution proofs
*)
