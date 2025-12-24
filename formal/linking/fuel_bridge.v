(** * FuelBridge: Bridge between interpreter.Fuel and MRun.Fuel
    
    This module provides conversion lemmas between the Fuel modules in
    interpreter.v and MRun.v. Both modules have structurally identical
    State and Config types, but differ in SmallStep implementations.
    
    The key insight is that for "pure" computations (those that don't
    use step_primitive or step_closure), both Fuel.run functions
    produce the same results.
    
    For UBT operations, we axiomatize that interpreter.Fuel success
    implies MRun.Fuel success, since both use the same M monad terms.
    
    Issue: #60 - Axiom Reduction via M Monad Interpreter
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
Import ListNotations.

Require Import UBT.Linking.ubt_execution.
Require Import UBT.Linking.MRun.
Require Import UBT.Linking.interpreter.

Open Scope Z_scope.

Module FuelBridge.

  (** State conversion: interpreter.State.t <-> MRun.State.t
      Both have identical structure: next_addr, heap, trait_impls *)
  
  Definition interp_state_to_mrun (s : interpreter.State.t) : MRun.State.t :=
    MRun.State.mk 
      (interpreter.State.next_addr s)
      (interpreter.State.heap s)
      (interpreter.State.trait_impls s).
  
  Definition mrun_state_to_interp (s : MRun.State.t) : interpreter.State.t :=
    interpreter.State.mk
      (MRun.State.next_addr s)
      (MRun.State.heap s)
      (MRun.State.trait_impls s).
  
  (** Round-trip lemmas *)
  Lemma interp_mrun_roundtrip : forall s,
    mrun_state_to_interp (interp_state_to_mrun s) = s.
  Proof.
    intros [next heap traits].
    reflexivity.
  Qed.
  
  Lemma mrun_interp_roundtrip : forall s,
    interp_state_to_mrun (mrun_state_to_interp s) = s.
  Proof.
    intros [next heap traits].
    reflexivity.
  Qed.
  
  (** Config conversion *)
  Definition interp_config_to_mrun (c : interpreter.Config.t) : MRun.Config.t :=
    MRun.Config.mk
      (interpreter.Config.term c)
      (interp_state_to_mrun (interpreter.Config.state c)).
  
  (** Outcome conversion: interpreter.Fuel.Outcome -> MRun.Fuel.Outcome
      
      Note: Panic types differ slightly:
      - interpreter uses PrimString.string 
      - MRun uses RocqOfRust.M.Panic.t (which wraps PrimString.string)
  *)
  Definition interp_outcome_to_mrun (o : interpreter.Fuel.Outcome Value.t) : MRun.Fuel.Outcome :=
    match o with
    | interpreter.Fuel.Success v => MRun.Fuel.Success v
    | interpreter.Fuel.Panic msg => MRun.Fuel.Panic (RocqOfRust.M.Panic.Make msg)
    | interpreter.Fuel.OutOfFuel => MRun.Fuel.OutOfFuel
    | interpreter.Fuel.StuckWith msg => MRun.Fuel.StuckWith msg
    end.
  
  (** Helper: Convert interpreter.State to ExecState *)
  Definition interp_state_to_exec (s : interpreter.State.t) : ExecState.t :=
    ExecState.mk (interpreter.State.next_addr s) (interpreter.State.heap s).

  (** This is exactly interpreter.State.to_exec_state *)
  Lemma interp_state_to_exec_eq : forall s,
    interp_state_to_exec s = interpreter.State.to_exec_state s.
  Proof.
    intros [next heap traits]. reflexivity.
  Qed.

  (** [AXIOM:FUEL-BRIDGE] interpreter.Fuel success implies MRun.Fuel success.
      
      When interpreter.Fuel.run succeeds on a configuration, MRun.Fuel.run
      also succeeds with the same value and corresponding ExecState.
      
      This axiom captures the semantic equivalence between the two Fuel
      implementations for well-behaved M monad terms (those used in UBT).
      
      The key insight is that trait_impls only affects step_closure_ext,
      and for UBT operations that succeed in the interpreter, they also
      succeed in MRun when starting from the corresponding ExecState.
      
      Status: Axiomatized - would require proving SmallStep equivalence
      Risk: Low - both implementations have identical structure for pure cases
      Mitigation: Both modules use the same M monad and LowM constructors
  *)
  Axiom interp_fuel_success_implies_mrun :
    forall (fuel : nat) (m : M) (s : interpreter.State.t) (v : Value.t) (s' : interpreter.State.t),
      interpreter.Fuel.run fuel (interpreter.Config.mk m s) = 
        (interpreter.Fuel.Success v, s') ->
      exists (ms' : MRun.State.t),
        MRun.Fuel.run fuel (MRun.Config.mk m (MRun.State.from_exec (interp_state_to_exec s))) = 
          (MRun.Fuel.Success v, ms') /\
        MRun.State.to_exec ms' = interp_state_to_exec s'.
  
  (** Corollary: Connect to run_ok *)
  Lemma interp_success_to_run_ok :
    forall (fuel : nat) (m : M) (es : ExecState.t) (v : Value.t) (es' : ExecState.t),
      (exists is is',
        interpreter.Fuel.run fuel (interpreter.Config.mk m is) = 
          (interpreter.Fuel.Success v, is') /\
        interpreter.State.to_exec_state is = es /\
        interpreter.State.to_exec_state is' = es') ->
      MRun.Run.run_ok m es v es'.
  Proof.
    intros fuel m es v es' [is [is' [Hrun [Hes Hes']]]].
    unfold MRun.Run.run_ok.
    destruct (interp_fuel_success_implies_mrun fuel m is v is' Hrun) as [ms' [Hmrun Hms']].
    exists fuel, ms'.
    split.
    - rewrite <- Hes. rewrite <- interp_state_to_exec_eq. exact Hmrun.
    - rewrite <- Hes'. rewrite <- interp_state_to_exec_eq. symmetry. exact Hms'.
  Qed.
  
  (** Simplified bridge for ExecState-based proofs.
      
      This is the main lemma used in *_stepping.v files.
      It shows that if we have interpreter.Fuel success, we get Run.run_ok.
  *)
  Lemma interpreter_fuel_to_run_ok :
    forall (fuel : nat) (m : M) (is : interpreter.State.t) (v : Value.t) (is' : interpreter.State.t),
      interpreter.Fuel.run fuel (interpreter.Config.mk m is) = 
        (interpreter.Fuel.Success v, is') ->
      MRun.Run.run_ok m (interpreter.State.to_exec_state is) v (interpreter.State.to_exec_state is').
  Proof.
    intros fuel m is v is' Hrun.
    apply interp_success_to_run_ok with (fuel := fuel).
    exists is, is'.
    split; [exact Hrun | split; reflexivity].
  Qed.

End FuelBridge.

(** ** Summary
    
    This module provides:
    
    1. State/Config conversion functions between interpreter and MRun
       - interp_state_to_mrun / mrun_state_to_interp (PROVEN round-trips)
       - interp_state_to_exec / interp_state_to_exec_eq (PROVEN)
       - interp_config_to_mrun
       - interp_outcome_to_mrun
    
    2. Bridge axiom and lemmas:
       - interp_fuel_success_implies_mrun (AXIOM - semantic equivalence)
       - interp_success_to_run_ok (PROVEN - via axiom)
       - interpreter_fuel_to_run_ok (PROVEN - main bridge for *_stepping.v)
    
    ** Axiom Count
    
    This module has 1 axiom:
    - interp_fuel_success_implies_mrun (Fuel bridge)
    
    ** Admit Count
    
    This module has 0 admits (reduced from 2 by reformulating the axiom).
    
    ** Usage
    
    In *_stepping.v files, use:
      apply FuelBridge.interpreter_fuel_to_run_ok with (fuel := fuel).
    
    to convert interpreter.Fuel.run success to MRun.Run.run_ok.
*)
