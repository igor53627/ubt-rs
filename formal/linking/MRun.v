(** * MRun: Relational Execution Semantics for M Monad
    
    This module provides a relational execution semantics for the M monad,
    designed to bridge with the rocq-of-rust-interp library's Fuel-based
    stepping semantics.
    
    ** Key Design Decision: Relational Semantics
    
    Instead of defining Run.run as a function (which would require handling
    divergence), we define a relational `run_ok` predicate:
    
      run_ok m s v s' := exists fuel,
        Fuel.run fuel (Config.mk m s) = (Success v, s')
    
    This allows us to:
    1. Prove monad laws directly via small-step semantics
    2. Avoid fuel policies in the interface
    3. Match the existential form of *_executes axioms
    
    ** Module Contents
    
    1. Config/StepResult types (matching MInterpreter)
    2. SmallStep evaluation
    3. Fuel-bounded execution
    4. Proven monad laws
    5. run_ok relation
    
    ** Integration with rocq-of-rust-interp
    
    When the rocq-of-rust-interp library is available, the types and
    definitions here are intended to be compatible. The library provides:
    - Complete step_primitive implementations
    - Complete step_closure implementations
    - Proven Laws module
    
    This module provides the bridge to UBT's ExecState.
    
    Issue: #60 - Axiom Reduction via M Monad Interpreter
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import UBT.Linking.ubt_execution.

Open Scope Z_scope.

(** ** Extended State with Trait Registry
    
    Extends ExecState with trait implementations for method resolution.
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

  Definition from_exec (s : ExecState.t) : t :=
    mk (ExecState.next_addr s) (ExecState.heap s) [].

  Definition to_exec (s : t) : ExecState.t :=
    ExecState.mk (next_addr s) (heap s).

  Lemma to_from_exec : forall s, to_exec (from_exec s) = s.
  Proof. intros [next h]. reflexivity. Qed.

End State.

(** ** Config Module *)

Module Config.
  Record t : Set := mk {
    term : M;
    state : State.t
  }.
End Config.

(** ** StepResult *)

Inductive StepResult : Set :=
| StepTo : Config.t -> StepResult
| Terminal : Value.t -> StepResult
| Exception : Exception.t -> StepResult
| Stuck : string -> StepResult.

(** ** SmallStep Module *)

Module SmallStep.

  Parameter step_primitive_ext : 
    RocqOfRust.M.Primitive.t -> (Value.t -> M) -> State.t -> option StepResult.
  
  Parameter step_closure_ext :
    Ty.t -> Value.t -> list Value.t -> 
    (Value.t + Exception.t -> M) -> State.t -> option StepResult.

  Definition step_let (e : M) (k : Value.t + Exception.t -> M) (s : State.t) : StepResult :=
    match e with
    | LowM.Pure (inl v) => StepTo (Config.mk (k (inl v)) s)
    | LowM.Pure (inr exn) => StepTo (Config.mk (k (inr exn)) s)
    | _ => Stuck "step_let: non-pure requires recursion"
    end.

  Definition step_primitive 
    (prim : RocqOfRust.M.Primitive.t) 
    (k : Value.t -> M) 
    (s : State.t) : StepResult :=
    match step_primitive_ext prim k s with
    | Some result => result
    | None => Stuck "primitive not implemented"
    end.

  Definition step (c : Config.t) : StepResult :=
    match Config.term c with
    | LowM.Pure (inl v) => Terminal v
    | LowM.Pure (inr exn) => Exception exn
    | LowM.Let _ty e k => step_let e k (Config.state c)
    | LowM.CallPrimitive prim k => step_primitive prim k (Config.state c)
    | LowM.CallClosure ty closure args k =>
        match step_closure_ext ty closure args k (Config.state c) with
        | Some result => result
        | None => Stuck "closure not implemented"
        end
    | _ => Stuck "term form not implemented"
    end.

End SmallStep.

(** ** Fuel Module *)

Module Fuel.

  Inductive Outcome : Set :=
  | Success : Value.t -> Outcome
  | Panic : RocqOfRust.M.Panic.t -> Outcome
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

(** ** Laws Module - Proven Monad Properties *)

Module Laws.

  Theorem run_pure : forall v s,
    Fuel.run 1 (Config.mk (LowM.Pure (inl v)) s) = (Fuel.Success v, s).
  Proof.
    intros v s. simpl. reflexivity.
  Qed.

  Theorem run_panic : forall msg s,
    Fuel.run 1 (Config.mk (LowM.Pure (inr (Exception.Panic msg))) s) = 
    (Fuel.Panic msg, s).
  Proof.
    intros msg s. simpl. reflexivity.
  Qed.

  Theorem step_deterministic : forall c r1 r2,
    SmallStep.step c = r1 ->
    SmallStep.step c = r2 ->
    r1 = r2.
  Proof.
    intros c r1 r2 H1 H2. rewrite H1 in H2. exact H2.
  Qed.

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
      destruct (SmallStep.step c) as [c' | v0 | exn | stuck_msg] eqn:Hstep.
      + destruct fuel2 as [|m]; [simpl in Hpanic; discriminate | ].
        simpl in Hpanic. rewrite Hstep in Hpanic.
        apply (IH _ Hsuccess _ Hpanic).
      + injection Hsuccess as _ _.
        destruct fuel2 as [|m]; [simpl in Hpanic; discriminate | ].
        simpl in Hpanic. rewrite Hstep in Hpanic. discriminate.
      + destruct exn; try discriminate.
      + discriminate.
  Qed.

  (** [AXIOM] Let sequence composition.
      
      When m terminates with v, and (k v) terminates with r,
      then (Let m k) terminates with r.
      
      This requires showing step correctly threads through let bindings.
      The proof would need step_let to handle non-pure cases via
      stepping the bound term first. *)
  Axiom let_sequence : forall (m : M) (k : Value.t -> M) (s : State.t),
    forall v s' fuel_m,
      Fuel.run fuel_m (Config.mk m s) = (Fuel.Success v, s') ->
      forall r s'' fuel_k,
        Fuel.run fuel_k (Config.mk (k v) s') = (Fuel.Success r, s'') ->
        exists fuel_total,
          Fuel.run fuel_total (Config.mk (LowM.Let (Ty.tuple []) m (fun ve => 
            match ve with
            | inl v' => k v'
            | inr _ => LowM.Pure (inr (Exception.Return (Value.Tuple [])))
            end)) s) = (Fuel.Success r, s'').

End Laws.

(** ** Run Module - Relational Execution Semantics *)

Module Run.

  Definition run_ok (m : M) (s : ExecState.t) (v : Value.t) (s' : ExecState.t) : Prop :=
    exists fuel is',
      Fuel.run fuel (Config.mk m (State.from_exec s)) = (Fuel.Success v, is')
      /\ s' = State.to_exec is'.

  Definition panics (m : M) (s : ExecState.t) (msg : RocqOfRust.M.Panic.t) : Prop :=
    exists fuel is',
      Fuel.run fuel (Config.mk m (State.from_exec s)) = (Fuel.Panic msg, is').

  Definition has_sufficient_fuel (m : M) (s : ExecState.t) : Prop :=
    exists v s', run_ok m s v s'.

  (** Pure values run to themselves *)
  Theorem run_pure_ok : forall v s,
    run_ok (LowM.Pure (inl v)) s v s.
  Proof.
    intros v s.
    unfold run_ok.
    exists 1%nat, (State.from_exec s).
    split.
    - apply Laws.run_pure.
    - apply State.to_from_exec.
  Qed.

  (** M.pure wrapper *)
  Theorem run_M_pure_ok : forall v s,
    run_ok (M.pure v) s v s.
  Proof.
    intros v s. unfold M.pure. apply run_pure_ok.
  Qed.

  (** Panic produces panic outcome *)
  Theorem run_panic_ok : forall msg s,
    panics (LowM.Pure (inr (Exception.Panic msg))) s msg.
  Proof.
    intros msg s.
    unfold panics.
    exists 1%nat, (State.from_exec s).
    apply Laws.run_panic.
  Qed.

  (** Run is deterministic *)
  Theorem run_deterministic : forall m s v1 s1 v2 s2,
    run_ok m s v1 s1 ->
    run_ok m s v2 s2 ->
    v1 = v2 /\ s1 = s2.
  Proof.
    intros m s v1 s1 v2 s2 H1 H2.
    unfold run_ok in *.
    destruct H1 as [fuel1 [is1 [Hrun1 Hproj1]]].
    destruct H2 as [fuel2 [is2 [Hrun2 Hproj2]]].
    assert (Hmax : exists fuel_max, (fuel1 <= fuel_max)%nat /\ (fuel2 <= fuel_max)%nat).
    { exists (max fuel1 fuel2). split; lia. }
    destruct Hmax as [fuel_max [Hle1 Hle2]].
    assert (H1' := Laws.fuel_monotonic _ _ _ _ _ Hle1 Hrun1).
    assert (H2' := Laws.fuel_monotonic _ _ _ _ _ Hle2 Hrun2).
    rewrite H1' in H2'. injection H2' as Hv His.
    subst. split; reflexivity.
  Qed.

  (** Success and panic are mutually exclusive *)
  Theorem success_precludes_panic : forall m s v s' msg,
    run_ok m s v s' ->
    panics m s msg ->
    False.
  Proof.
    intros m s v s' msg Hsuccess Hpanic.
    unfold run_ok, panics in *.
    destruct Hsuccess as [fuel1 [is1 [Hrun1 _]]].
    destruct Hpanic as [fuel2 [is2 Hrun2]].
    eapply Laws.success_precludes_panic; eauto.
  Qed.

End Run.

(** ** Summary
    
    This module provides:
    
    1. State: Extended state with trait registry
    2. Config/StepResult: Execution configuration
    3. SmallStep: Single-step evaluation (with extension points)
    4. Fuel: Bounded execution
    5. Laws: Proven monad properties
       - run_pure (PROVEN)
       - run_panic (PROVEN)
       - fuel_monotonic (PROVEN)
       - success_precludes_panic (PROVEN)
       - let_sequence (AXIOM - central axiom)
    6. Run: Relational execution semantics
       - run_ok relation
       - run_pure_ok (PROVEN)
       - run_M_pure_ok (PROVEN)
       - run_panic_ok (PROVEN)
       - run_deterministic (PROVEN)
       - success_precludes_panic (PROVEN)
    
    ** Axiom Count
    
    This module has 1 axiom (let_sequence) and 2 parameters
    (step_primitive_ext, step_closure_ext).
    
    ** Integration Path
    
    When rocq-of-rust-interp is fully integrated:
    1. Replace step_primitive_ext with library implementation
    2. Replace step_closure_ext with library implementation
    3. Replace let_sequence axiom with library proof (when available)
    
    ** FuelBridge (in fuel_bridge.v)
    
    The FuelBridge module is in a separate file (fuel_bridge.v) to avoid
    circular dependencies. It provides the bridge between interpreter.Fuel
    and MRun.Fuel for the *_stepping.v files.
*)
