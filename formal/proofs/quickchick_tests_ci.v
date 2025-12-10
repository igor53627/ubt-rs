(** * QuickChick CI Tests - Reduced test count for CI
    
    This is a CI-optimized version of quickchick_tests.v with reduced
    test counts (1000 per property instead of 10000) for faster CI builds.
    
    For local development with full test coverage, use quickchick_tests.v.
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import UBT.Sim.tree.

Open Scope Z_scope.

From QuickChick Require Import QuickChick.
Import QcNotation.

(** ** CI Configuration: 1000 tests per property *)
Extract Constant Test.defNumTests => "1000".

(** Import definitions from main quickchick_tests *)

Definition key_eqb (k1 k2 : TreeKey) : bool :=
  stem_eq (tk_stem k1) (tk_stem k2) && Z.eqb (tk_subindex k1) (tk_subindex k2).

Definition value_eqb (v1 v2 : Value) : bool :=
  List.forallb (fun p => Z.eqb (fst p) (snd p)) (List.combine v1 v2) 
  && Nat.eqb (List.length v1) (List.length v2).

Definition option_value_eqb (ov1 ov2 : option Value) : bool :=
  match ov1, ov2 with
  | None, None => true
  | Some v1, Some v2 => value_eqb v1 v2
  | _, _ => false
  end.

Definition gen_stem_from_seed (seed : Z) : Stem :=
  mkStem (map (fun i => Z.modulo (seed + Z.of_nat i) 256) (seq 0 31)).

Definition gen_stem_from_byte := gen_stem_from_seed.

Definition gen_key_from_bytes (stem_seed : Z) (idx : Z) : TreeKey :=
  mkTreeKey (gen_stem_from_seed stem_seed) (Z.modulo idx 256).

Definition gen_nonzero_value (seed : Z) : Value :=
  map (fun i => Z.modulo (seed + Z.of_nat i) 255 + 1) (seq 0 32).

Definition gen_zero_value : Value := zero32.

(** Property definitions *)
Definition prop_get_insert_same (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  if is_zero_value v then true
  else option_value_eqb (sim_tree_get (sim_tree_insert t k v) k) (Some v).

Definition prop_get_insert_other (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if key_eqb k1 k2 then true
  else option_value_eqb (sim_tree_get (sim_tree_insert t k1 v) k2) (sim_tree_get t k2).

Definition prop_insert_delete (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  option_value_eqb (sim_tree_get (sim_tree_delete (sim_tree_insert t k v) k) k) None.

Definition prop_insert_idempotent (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  let t1 := sim_tree_insert t k v in
  let t2 := sim_tree_insert t1 k v in
  option_value_eqb (sim_tree_get t1 k) (sim_tree_get t2 k).

Definition prop_empty_get (k : TreeKey) : bool :=
  option_value_eqb (sim_tree_get empty_tree k) None.

(** Generators *)
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

(** Shrinkers *)
#[export] Instance shrinkStem : Shrink Stem := 
  {| shrink := fun s => 
       [mkStem (repeat 0 31); gen_stem_from_byte 0; gen_stem_from_byte 1] |}.

#[export] Instance shrinkTreeKey : Shrink TreeKey := 
  {| shrink := fun k =>
       let simpler_stems := shrink (tk_stem k) in
       map (fun s => mkTreeKey s (tk_subindex k)) simpler_stems ++
       [mkTreeKey (tk_stem k) 0; mkTreeKey (gen_stem_from_byte 0) 0] |}.

#[export] Instance shrinkValue : Shrink Value := 
  {| shrink := fun v =>
       if is_zero_value v then [] 
       else [zero32; gen_nonzero_value 1] |}.

#[export] Instance shrinkSimTree : Shrink SimTree := 
  {| shrink := fun _ => [empty_tree] |}.

(** Show instances *)
#[export] Instance showStem : Show Stem :=
  {| show := fun s => "Stem[...]"%string |}.

#[export] Instance showTreeKey : Show TreeKey :=
  {| show := fun k => "Key{...}"%string |}.

#[export] Instance showValue : Show Value :=
  {| show := fun v => if is_zero_value v then "zero32"%string else "Value[...]"%string |}.

#[export] Instance showSimTree : Show SimTree :=
  {| show := fun t => "SimTree{...}"%string |}.

(** Run tests - 1000 each = 5000 total *)
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

(** End of quickchick_tests_ci.v *)
