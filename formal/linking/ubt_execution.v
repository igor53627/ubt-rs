(** * UBT Execution: Shared Execution State and Outcome Types
    
    This module defines types shared between operations.v and interpreter.v,
    breaking the dependency cycle that previously prevented Run.run from
    being defined in terms of Fuel.run.
    
    ** Why This Module Exists
    
    Previously:
    - operations.v defined ExecState and Outcome
    - interpreter.v imported operations.v and defined State, Fuel, etc.
    - operations.v could not import interpreter.v (cycle)
    
    Now:
    - This module defines ExecState and Outcome
    - Both operations.v and interpreter.v import this module
    - operations.v can import interpreter.v (no cycle)
    - Run.run can be defined as Fuel.run wrapper
    
    ** Module Contents
    
    1. Outcome - Result type for monadic execution (Success/Panic/Diverge)
    2. ExecState - Heap memory model for M monad evaluation
    
    Issue: #24 - Break dependency cycle for Run.run definition
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
Import ListNotations.

Open Scope Z_scope.

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

(** ** Outcome for Value.t Results *)

Definition ValueOutcome := Outcome.t Value.t.
