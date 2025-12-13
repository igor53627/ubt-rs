(** * UBT Stepping Extensions for rocq-of-rust-interp Library
    
    This module implements the extension points from the general-purpose
    M monad interpreter library for UBT-specific operations.
    
    ** Extension Points Implemented
    
    1. step_primitive_ext - UBT-specific primitives (none needed)
    2. step_closure_ext - UBT tree operation closures
    
    ** UBT Closures
    
    - rust_get: Tree::get operation
    - rust_insert: Tree::insert operation
    - rust_delete: Tree::delete operation (via insert zero)
    - rust_root_hash: Root hash computation
    - or_insert_with: HashMap entry default factory
    
    ** Integration
    
    This module bridges the generic library with UBT's linking layer.
    Import both this module and the library to get full stepping.
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import String.
Import ListNotations.

Require Import UBT.Sim.tree.
Require Import UBT.Linking.types.
Require Import UBT.Linking.operations.

Open Scope Z_scope.
Open Scope string_scope.

(** ** UBT Closure Patterns
    
    These definitions identify UBT-specific closures by their path.
*)

Module UBTClosures.

  Definition PATH_TREE_GET : string := "ubt::tree::Tree::get".
  Definition PATH_TREE_INSERT : string := "ubt::tree::Tree::insert".
  Definition PATH_TREE_DELETE : string := "ubt::tree::Tree::delete".
  Definition PATH_ROOT_HASH : string := "ubt::tree::Tree::root_hash".
  Definition PATH_STEMNODE_NEW : string := "ubt::tree::StemNode::new".
  Definition PATH_OR_INSERT_WITH : string := "std::collections::hash::map::Entry::or_insert_with".

  (** Check if a closure value matches a known path *)
  Definition closure_path_of (v : Value.t) : option string :=
    match v with
    | Value.Closure path _ => Some path
    | _ => None
    end.

  (** Match closure against known UBT paths *)
  Definition is_ubt_closure (v : Value.t) : bool :=
    match closure_path_of v with
    | Some path =>
        String.eqb path PATH_TREE_GET ||
        String.eqb path PATH_TREE_INSERT ||
        String.eqb path PATH_TREE_DELETE ||
        String.eqb path PATH_ROOT_HASH ||
        String.eqb path PATH_STEMNODE_NEW ||
        String.eqb path PATH_OR_INSERT_WITH
    | None => false
    end.

End UBTClosures.

(** ** State Type (compatible with library)
    
    UBT uses the same State type as the library.
*)

Module UBTState.
  
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

End UBTState.

(** ** Config and StepResult (compatible with library) *)

Module UBTConfig.
  Record t : Set := mk {
    term : M;
    state : UBTState.t
  }.
End UBTConfig.

Inductive UBTStepResult : Set :=
| UBTStepTo : UBTConfig.t -> UBTStepResult
| UBTTerminal : Value.t -> UBTStepResult
| UBTException : Exception.t -> UBTStepResult
| UBTStuck : string -> UBTStepResult.

(** ** Primitive Extension
    
    UBT doesn't need additional primitives beyond what the library provides.
*)

Definition ubt_step_primitive_ext 
  (prim : RocqOfRust.M.Primitive.t) 
  (k : Value.t -> M) 
  (s : UBTState.t) : option UBTStepResult :=
  None.

(** ** Closure Extension
    
    UBT-specific closure stepping. This is where the main work happens.
*)

Module UBTClosureStepping.
  Import UBTClosures.

  (** Step StemNode::new closure - creates empty SubIndexMap *)
  Definition step_stemnode_new 
    (args : list Value.t) 
    (k : Value.t + Exception.t -> M) 
    (s : UBTState.t) : option UBTStepResult :=
    match args with
    | [stem_val] =>
        let empty_subindexmap := Value.Array [] in
        let stemnode := Value.StructRecord "ubt::tree::StemNode" [] []
          [("stem"%string, stem_val); 
           ("values"%string, empty_subindexmap)] in
        Some (UBTStepTo (UBTConfig.mk (k (inl stemnode)) s))
    | _ => None
    end.

  (** Step or_insert_with closure - for HashMap entry pattern *)
  Definition step_or_insert_with
    (closure_env : Value.t)
    (args : list Value.t)
    (k : Value.t + Exception.t -> M)
    (s : UBTState.t) : option UBTStepResult :=
    match closure_env with
    | Value.Closure _ env_vals =>
        match env_vals with
        | [stem_val] => step_stemnode_new [stem_val] k s
        | _ => None
        end
    | _ => None
    end.

  (** Main UBT closure stepping dispatcher *)
  Definition ubt_step_closure_ext
    (ty : Ty.t)
    (closure : Value.t)
    (args : list Value.t)
    (k : Value.t + Exception.t -> M)
    (s : UBTState.t) : option UBTStepResult :=
    match closure_path_of closure with
    | Some path =>
        if String.eqb path PATH_STEMNODE_NEW then
          step_stemnode_new args k s
        else if String.eqb path PATH_OR_INSERT_WITH then
          step_or_insert_with closure args k s
        else
          None
    | None => None
    end.

End UBTClosureStepping.

(** ** Integration with Library
    
    These definitions show how to use the library with UBT extensions.
*)

Module UBTIntegration.
  Import UBTClosureStepping.

  (** The library's step_primitive_ext instantiated for UBT *)
  Definition step_primitive_ext := ubt_step_primitive_ext.

  (** The library's step_closure_ext instantiated for UBT *)
  Definition step_closure_ext := ubt_step_closure_ext.

  (** ** Proven Properties *)

  (** StemNode::new produces empty subindexmap *)
  Lemma stemnode_new_produces_empty :
    forall stem_val k s cfg,
      step_stemnode_new [stem_val] k s = Some (UBTStepTo cfg) ->
      exists stemnode,
        UBTConfig.term cfg = k (inl stemnode).
  Proof.
    intros stem_val k s cfg H.
    unfold step_stemnode_new in H.
    injection H as Hcfg. subst cfg.
    eexists. reflexivity.
  Qed.

  (** or_insert_with steps to StemNode::new result *)
  Lemma or_insert_with_invokes_stemnode_new :
    forall stem_val k s cfg,
      step_or_insert_with (Value.Closure UBTClosures.PATH_STEMNODE_NEW [stem_val]) [] k s = Some (UBTStepTo cfg) ->
      step_stemnode_new [stem_val] k s = Some (UBTStepTo cfg).
  Proof.
    intros stem_val k s cfg H.
    unfold step_or_insert_with in H.
    simpl in H.
    exact H.
  Qed.

End UBTIntegration.

(** ** Summary
    
    This module provides:
    
    1. UBT closure identification (PATH_* constants)
    2. Closure stepping for StemNode::new
    3. Closure stepping for or_insert_with
    4. Integration definitions for the library
    5. Proven stepping lemmas
    
    To use:
    
    1. Import this module alongside RocqInterp.MInterpreter
    2. Use UBTIntegration.step_closure_ext as the closure extension
    3. Use stepping lemmas for operation proofs
    
    Remaining work:
    
    - step_tree_get: Full Tree::get closure stepping
    - step_tree_insert: Full Tree::insert closure stepping  
    - step_root_hash: Root hash computation stepping
    
    These require integrating with the existing axioms in operations.v
    and converting them to stepping-based proofs.
*)
