(** * QuickChick Property-Based Tests for UBT
    
    This module provides property-based testing for the UBT simulation layer
    using QuickChick, a randomized testing framework for Coq/Rocq.
    
    ## Installation
    
    QuickChick is not installed by default. To install:
    
    ```bash
    eval $(opam env --switch=rocq-9)
    opam install coq-quickchick
    ```
    
    Then rebuild the project:
    
    ```bash
    make clean && make all
    ```
    
    ## Running Tests
    
    Load this file in CoqIDE or Proof General and execute the QuickChick commands,
    or run from command line:
    
    ```bash
    coqc -Q specs UBT.Specs -Q simulations UBT.Sim -Q proofs UBT.Proofs proofs/quickchick_tests.v
    ```
    
    Note: QuickChick tests are interactive and require compilation with extraction.
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** Import our simulation layer *)
Require Import UBT.Sim.tree.

Open Scope Z_scope.

(** ** QuickChick Imports *)

From QuickChick Require Import QuickChick.
Import QcNotation.

(** ** Decidable Equality Instances *)

(** Boolean equality for TreeKey (same stem and same subindex) *)
Definition key_eqb (k1 k2 : TreeKey) : bool :=
  stem_eq (tk_stem k1) (tk_stem k2) && Z.eqb (tk_subindex k1) (tk_subindex k2).

(** Boolean equality for Value (list of Z) *)
Definition value_eqb (v1 v2 : Value) : bool :=
  List.forallb (fun p => Z.eqb (fst p) (snd p)) (List.combine v1 v2) 
  && Nat.eqb (List.length v1) (List.length v2).

(** Boolean equality for option Value *)
Definition option_value_eqb (ov1 ov2 : option Value) : bool :=
  match ov1, ov2 with
  | None, None => true
  | Some v1, Some v2 => value_eqb v1 v2
  | _, _ => false
  end.

(** ** Show Instances (for debugging failed tests)
    
    Note: Full Show instances require Ascii/String imports.
    These are placeholder definitions - implement when QuickChick is installed.
*)

(** ** Test Generators
    
    When QuickChick is available, these will generate random test inputs.
    For now, we define helper functions that could be used as generators.
*)

(** Generate a stem with given seed byte *)
Definition gen_stem_from_byte (seed : Z) : Stem :=
  mkStem (repeat (Z.modulo seed 256) 31).

(** Generate a key from two seed bytes *)
Definition gen_key_from_bytes (stem_seed : Z) (idx : Z) : TreeKey :=
  mkTreeKey (gen_stem_from_byte stem_seed) (Z.modulo idx 256).

(** Generate a nonzero value from a seed *)
Definition gen_nonzero_value (seed : Z) : Value :=
  let byte := Z.modulo (seed + 1) 255 + 1 in
  repeat byte 32.

(** Generate a zero value *)
Definition gen_zero_value : Value := zero32.

(** ** Property Definitions
    
    These properties will be tested with QuickChick.
*)

(** Property 1: get (insert t k v) k = Some v (when v is nonzero) *)
Definition prop_get_insert_same (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  if is_zero_value v then
    true
  else
    option_value_eqb (sim_tree_get (sim_tree_insert t k v) k) (Some v).

(** Property 2: get (insert t k1 v) k2 = get t k2 (when k1 <> k2) *)
Definition prop_get_insert_other (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if key_eqb k1 k2 then
    true
  else
    option_value_eqb (sim_tree_get (sim_tree_insert t k1 v) k2) (sim_tree_get t k2).

(** Property 3: get (delete (insert t k v) k) k = None *)
Definition prop_insert_delete (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  option_value_eqb (sim_tree_get (sim_tree_delete (sim_tree_insert t k v) k) k) None.

(** Property 4: insert (insert t k v) k v = insert t k v (idempotent at key) *)
Definition prop_insert_idempotent (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  let t1 := sim_tree_insert t k v in
  let t2 := sim_tree_insert t1 k v in
  option_value_eqb (sim_tree_get t1 k) (sim_tree_get t2 k).

(** Property 5: get empty_tree k = None *)
Definition prop_empty_get (k : TreeKey) : bool :=
  option_value_eqb (sim_tree_get empty_tree k) None.

(** ** Manual Test Cases
    
    Until QuickChick is installed, we can verify properties on specific examples.
*)

(** Test stems *)
Definition test_stem_1 : Stem := gen_stem_from_byte 1.
Definition test_stem_2 : Stem := gen_stem_from_byte 2.

(** Test keys *)
Definition test_key_1 : TreeKey := gen_key_from_bytes 1 0.
Definition test_key_2 : TreeKey := gen_key_from_bytes 1 1.
Definition test_key_3 : TreeKey := gen_key_from_bytes 2 0.

(** Test values *)
Definition test_value_1 : Value := gen_nonzero_value 42.
Definition test_value_2 : Value := gen_nonzero_value 99.

(** Manual test: prop_get_insert_same on empty tree *)
Example test_get_insert_same_1 :
  prop_get_insert_same empty_tree test_key_1 test_value_1 = true.
Proof. reflexivity. Qed.

(** Manual test: prop_empty_get *)
Example test_empty_get_1 :
  prop_empty_get test_key_1 = true.
Proof. reflexivity. Qed.

(** Manual test: prop_insert_delete *)
Example test_insert_delete_1 :
  prop_insert_delete empty_tree test_key_1 test_value_1 = true.
Proof. reflexivity. Qed.

(** Manual test: prop_get_insert_other with different stems *)
Example test_get_insert_other_stems :
  prop_get_insert_other empty_tree test_key_1 test_key_3 test_value_1 = true.
Proof. reflexivity. Qed.

(** Manual test: prop_insert_idempotent *)
Example test_insert_idempotent_1 :
  prop_insert_idempotent empty_tree test_key_1 test_value_1 = true.
Proof. reflexivity. Qed.

(** ** QuickChick Test Commands *)

(* Generators - using QuickChick 2.x API *)

#[export] Instance genStem : Gen Stem :=
  {| arbitrary :=
       bindGen arbitrary (fun seed : Z =>
         returnGen (gen_stem_from_byte seed)) |}.

#[export] Instance genTreeKey : Gen TreeKey :=
  {| arbitrary :=
       bindGen arbitrary (fun stem_seed : Z =>
         bindGen arbitrary (fun idx : Z =>
           returnGen (gen_key_from_bytes stem_seed idx))) |}.

#[export] Instance genValue : Gen Value :=
  {| arbitrary :=
       freq [ (9%nat, bindGen arbitrary (fun seed : Z => returnGen (gen_nonzero_value seed)))
            ; (1%nat, returnGen gen_zero_value)
            ] |}.

#[export] Instance genSimTree : Gen SimTree :=
  {| arbitrary :=
       bindGen (choose (0, 5)%nat) (fun n =>
         List.fold_right (fun _ acc =>
           bindGen acc (fun t =>
             bindGen arbitrary (fun k : TreeKey =>
               bindGen arbitrary (fun v : Value =>
                 returnGen (sim_tree_insert t k v)))))
         (returnGen empty_tree)
         (List.repeat tt n)) |}.

(* Shrinkers - basic implementations to help debug failing tests *)

#[export] Instance shrinkStem : Shrink Stem := 
  {| shrink := fun s => 
       (* Shrink to simpler stems: try zero stem and stems with smaller values *)
       [mkStem (repeat 0 31); gen_stem_from_byte 0; gen_stem_from_byte 1] |}.

#[export] Instance shrinkTreeKey : Shrink TreeKey := 
  {| shrink := fun k =>
       (* Shrink to simpler keys: try subindex 0, and simpler stems *)
       let simpler_stems := shrink (tk_stem k) in
       map (fun s => mkTreeKey s (tk_subindex k)) simpler_stems ++
       [mkTreeKey (tk_stem k) 0; mkTreeKey (gen_stem_from_byte 0) 0] |}.

#[export] Instance shrinkValue : Shrink Value := 
  {| shrink := fun v =>
       (* Shrink to zero value or simpler non-zero values *)
       if is_zero_value v then [] 
       else [zero32; gen_nonzero_value 1] |}.

#[export] Instance shrinkSimTree : Shrink SimTree := 
  {| shrink := fun _ => 
       (* Trees are complex; shrink to empty tree *)
       [empty_tree] |}.

(* Show instances *)

#[export] Instance showStem : Show Stem :=
  {| show := fun s => "Stem[...]"%string |}.

#[export] Instance showTreeKey : Show TreeKey :=
  {| show := fun k => "Key{...}"%string |}.

#[export] Instance showValue : Show Value :=
  {| show := fun v => if is_zero_value v then "zero32"%string else "Value[...]"%string |}.

#[export] Instance showSimTree : Show SimTree :=
  {| show := fun t => "SimTree{...}"%string |}.

(* Property-based tests *)

QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_get_insert_same t k v)))).

QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v : Value =>
        prop_get_insert_other t k1 k2 v))))).

QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_insert_delete t k v)))).

QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_insert_idempotent t k v)))).

QuickChick (forAll arbitrary (fun k : TreeKey =>
  prop_empty_get k)).

(** ** Theorem Statements (proved in tree.v)
    
    These theorems correspond to our properties.
    QuickChick helps us gain confidence before investing in proofs.
*)

Check get_insert_same.
Check get_empty.
Check get_delete.

(** End of quickchick_tests.v *)
