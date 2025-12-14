(** * QuickChick CI Tests - Reduced test count for CI
    
    This is a CI-optimized version of quickchick_tests.v with reduced
    test counts (500 per property instead of 10000) for faster CI builds.
    
    For local development with full test coverage, use quickchick_tests.v.
    
    Properties: 26 (14 core + 12 edge case)
    Tests per property: 500
    Total tests: 13,000
*)

From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.
Import ListNotations.

Require Import UBT.Sim.tree.

Open Scope Z_scope.

From QuickChick Require Import QuickChick.
Import QcNotation.

(** ** CI Configuration: 500 tests per property *)
Extract Constant Test.defNumTests => "500".

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

(** Additional properties *)

Definition prop_insert_preserves_other_stems (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if stem_eq (tk_stem k1) (tk_stem k2) then true
  else option_value_eqb (sim_tree_get (sim_tree_insert t k1 v) k2) (sim_tree_get t k2).

Definition prop_batch_operations_commute (t : SimTree) (k1 k2 : TreeKey) (v1 v2 : Value) : bool :=
  if key_eqb k1 k2 then true
  else
    let t1 := sim_tree_insert (sim_tree_insert t k1 v1) k2 v2 in
    let t2 := sim_tree_insert (sim_tree_insert t k2 v2) k1 v1 in
    option_value_eqb (sim_tree_get t1 k1) (sim_tree_get t2 k1) &&
    option_value_eqb (sim_tree_get t1 k2) (sim_tree_get t2 k2).

Definition prop_delete_idempotent (t : SimTree) (k : TreeKey) : bool :=
  let t1 := sim_tree_delete t k in
  let t2 := sim_tree_delete t1 k in
  option_value_eqb (sim_tree_get t1 k) (sim_tree_get t2 k).

Definition prop_zero_insert_is_delete (t : SimTree) (k : TreeKey) : bool :=
  option_value_eqb 
    (sim_tree_get (sim_tree_insert t k zero32) k) 
    (sim_tree_get (sim_tree_delete t k) k).

Definition prop_last_insert_wins (t : SimTree) (k : TreeKey) (v1 v2 : Value) : bool :=
  if is_zero_value v2 then
    option_value_eqb (sim_tree_get (sim_tree_insert (sim_tree_insert t k v1) k v2) k) None
  else
    option_value_eqb (sim_tree_get (sim_tree_insert (sim_tree_insert t k v1) k v2) k) (Some v2).

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

(* Property 6: Insert preserves other stems *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v : Value =>
        prop_insert_preserves_other_stems t k1 k2 v))))).

(* Property 7: Batch operations commute *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v1 : Value =>
        forAll arbitrary (fun v2 : Value =>
          prop_batch_operations_commute t k1 k2 v1 v2)))))).

(* Property 8: Delete idempotent *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    prop_delete_idempotent t k))).

(* Property 9: Zero insert is delete *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    prop_zero_insert_is_delete t k))).

(* Property 10: Last insert wins *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v1 : Value =>
      forAll arbitrary (fun v2 : Value =>
        prop_last_insert_wins t k v1 v2))))).

(** ** Edge Case Properties (Properties 11-22) *)

(** Property 11: Subindex independence *)
Definition prop_subindex_independence (t : SimTree) (stem_seed : Z) (idx1 idx2 : Z) (v : Value) : bool :=
  let s := gen_stem_from_seed stem_seed in
  let k1 := mkTreeKey s (Z.modulo idx1 256) in
  let k2 := mkTreeKey s (Z.modulo idx2 256) in
  if Z.eqb (Z.modulo idx1 256) (Z.modulo idx2 256) then true
  else option_value_eqb (sim_tree_get (sim_tree_insert t k1 v) k2) (sim_tree_get t k2).

(** Property 12: Empty tree has no stems *)
Definition prop_empty_tree_no_stems (s : Stem) : bool :=
  match stems_get (st_stems empty_tree) s with
  | None => true
  | Some _ => false
  end.

(** Property 13: Maximum subindex (255) operations work correctly *)
Definition prop_max_subindex_works (t : SimTree) (stem_seed : Z) (v : Value) : bool :=
  let s := gen_stem_from_seed stem_seed in
  let k := mkTreeKey s 255 in
  if is_zero_value v then true
  else option_value_eqb (sim_tree_get (sim_tree_insert t k v) k) (Some v).

(** Property 14: Stems differing only in last bit are distinguished *)
Definition prop_similar_stems_distinguished (t : SimTree) (seed : Z) (idx : Z) (v1 v2 : Value) : bool :=
  let base_bytes := map (fun i => Z.modulo (seed + Z.of_nat i) 256) (seq 0 30) in
  let s1 := mkStem (base_bytes ++ [0]) in
  let s2 := mkStem (base_bytes ++ [1]) in
  let k1 := mkTreeKey s1 (Z.modulo idx 256) in
  let k2 := mkTreeKey s2 (Z.modulo idx 256) in
  if is_zero_value v1 then true
  else
    let t' := sim_tree_insert (sim_tree_insert t k1 v1) k2 v2 in
    option_value_eqb (sim_tree_get t' k1) (Some v1).

(** Property 15: Boundary subindex transitions *)
Definition prop_boundary_subindex_transitions (t : SimTree) (stem_seed : Z) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let s := gen_stem_from_seed stem_seed in
    let k0 := mkTreeKey s 0 in
    let k255 := mkTreeKey s 255 in
    let t' := sim_tree_insert (sim_tree_insert t k0 v) k255 v in
    option_value_eqb (sim_tree_get t' k0) (Some v) &&
    option_value_eqb (sim_tree_get t' k255) (Some v).

(** Property 16: Overwrite then delete leaves no trace *)
Definition prop_overwrite_delete_clean (t : SimTree) (k : TreeKey) (v1 v2 : Value) : bool :=
  let t1 := sim_tree_delete (sim_tree_insert (sim_tree_insert t k v1) k v2) k in
  option_value_eqb (sim_tree_get t1 k) None.

(** Property 17: Multiple stems with interleaved operations *)
Definition prop_interleaved_multi_stem (stem_seed1 stem_seed2 : Z) (v1 v2 : Value) : bool :=
  if is_zero_value v1 || is_zero_value v2 then true
  else
    let s1 := gen_stem_from_seed stem_seed1 in
    let s2 := gen_stem_from_seed stem_seed2 in
    if stem_eq s1 s2 then true
    else
      let k1_0 := mkTreeKey s1 0 in
      let k2_0 := mkTreeKey s2 0 in
      let t := sim_tree_insert (sim_tree_insert empty_tree k1_0 v1) k2_0 v2 in
      option_value_eqb (sim_tree_get t k1_0) (Some v1) &&
      option_value_eqb (sim_tree_get t k2_0) (Some v2).

(** Property 18: Delete non-existent key is no-op *)
Definition prop_delete_nonexistent_noop (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if key_eqb k1 k2 then true
  else if is_zero_value v then true
  else
    let t1 := sim_tree_insert t k1 v in
    let t2 := sim_tree_delete t1 k2 in
    option_value_eqb (sim_tree_get t2 k1) (Some v).

(** Property 19: High-bit stem works *)
Definition prop_high_bit_stem_works (t : SimTree) (idx : Z) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let s := mkStem (repeat 128 31) in
    let k := mkTreeKey s (Z.modulo idx 256) in
    option_value_eqb (sim_tree_get (sim_tree_insert t k v) k) (Some v).

(** Property 20: Insert-delete roundtrip *)
Definition prop_insert_delete_roundtrip (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let t' := sim_tree_delete (sim_tree_insert t k v) k in
    option_value_eqb (sim_tree_get t' k) None.

(** Property 21: Stem colocation *)
Definition prop_stem_colocation (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if stem_eq (tk_stem k1) (tk_stem k2) then
    let t' := sim_tree_insert t k1 v in
    match stems_get (st_stems t') (tk_stem k1), stems_get (st_stems t') (tk_stem k2) with
    | Some m1, Some m2 => true
    | _, _ => false
    end
  else true.

(** Property 22: Batch vs individual equivalence (distinct keys only) *)
Definition prop_batch_then_individual (t : SimTree) (k1 k2 : TreeKey) (v1 v2 : Value) : bool :=
  if key_eqb k1 k2 then true
  else
    let t_batch := sim_tree_insert (sim_tree_insert t k1 v1) k2 v2 in
    let check1 := option_value_eqb (sim_tree_get t_batch k1) 
                    (if is_zero_value v1 then None else Some v1) in
    let check2 := option_value_eqb (sim_tree_get t_batch k2) 
                    (if is_zero_value v2 then None else Some v2) in
    check1 && check2.

(** ** Edge Case QuickChick Tests *)

(* Property 11: Subindex independence *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun stem_seed : Z =>
    forAll arbitrary (fun idx1 : Z =>
      forAll arbitrary (fun idx2 : Z =>
        forAll arbitrary (fun v : Value =>
          prop_subindex_independence t stem_seed idx1 idx2 v)))))).

(* Property 12: Empty tree has no stems *)
QuickChick (forAll arbitrary (fun s : Stem =>
  prop_empty_tree_no_stems s)).

(* Property 13: Maximum subindex (255) operations *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun stem_seed : Z =>
    forAll arbitrary (fun v : Value =>
      prop_max_subindex_works t stem_seed v)))).

(* Property 14: Similar stems distinguished *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun seed : Z =>
    forAll arbitrary (fun idx : Z =>
      forAll arbitrary (fun v1 : Value =>
        forAll arbitrary (fun v2 : Value =>
          prop_similar_stems_distinguished t seed idx v1 v2)))))).

(* Property 15: Boundary subindex transitions *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun stem_seed : Z =>
    forAll arbitrary (fun v : Value =>
      prop_boundary_subindex_transitions t stem_seed v)))).

(* Property 16: Overwrite then delete *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v1 : Value =>
      forAll arbitrary (fun v2 : Value =>
        prop_overwrite_delete_clean t k v1 v2))))).

(* Property 17: Interleaved multi-stem *)
QuickChick (forAll arbitrary (fun stem_seed1 : Z =>
  forAll arbitrary (fun stem_seed2 : Z =>
    forAll arbitrary (fun v1 : Value =>
      forAll arbitrary (fun v2 : Value =>
        prop_interleaved_multi_stem stem_seed1 stem_seed2 v1 v2))))).

(* Property 18: Delete non-existent key is no-op *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v : Value =>
        prop_delete_nonexistent_noop t k1 k2 v))))).

(* Property 19: High-bit stem works *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun idx : Z =>
    forAll arbitrary (fun v : Value =>
      prop_high_bit_stem_works t idx v)))).

(* Property 20: Insert-delete roundtrip *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_insert_delete_roundtrip t k v)))).

(* Property 21: Stem colocation *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v : Value =>
        prop_stem_colocation t k1 k2 v))))).

(* Property 22: Batch vs individual equivalence *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v1 : Value =>
        forAll arbitrary (fun v2 : Value =>
          prop_batch_then_individual t k1 k2 v1 v2)))))).

(** End of quickchick_tests_ci.v - 22 properties x 500 = 11,000 tests *)
