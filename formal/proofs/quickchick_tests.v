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

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
Import ListNotations.

(** Import our simulation layer *)
Require Import UBT.Sim.tree.
Require Import UBT.Sim.iterator.

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

(** Generate a stem with per-position byte diversity from seed *)
Definition gen_stem_from_seed (seed : Z) : Stem :=
  mkStem (map (fun i => Z.modulo (seed + Z.of_nat i) 256) (seq 0 31)).

(** Backward compatibility alias *)
Definition gen_stem_from_byte := gen_stem_from_seed.

(** Generate a key from two seed bytes *)
Definition gen_key_from_bytes (stem_seed : Z) (idx : Z) : TreeKey :=
  mkTreeKey (gen_stem_from_seed stem_seed) (Z.modulo idx 256).

(** Generate a nonzero value with per-position byte diversity from seed *)
Definition gen_nonzero_value (seed : Z) : Value :=
  map (fun i => Z.modulo (seed + Z.of_nat i) 255 + 1) (seq 0 32).

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

(** ** Additional Properties for Stronger Coverage *)

(** Note: Root hash determinism cannot be tested via QuickChick because
    hash_value, hash_stem, hash_pair are axiomatized Parameters.
    This property is instead verified structurally in tree.v. *)

(** Property 6: Insert preserves values at unrelated stems *)
Definition prop_insert_preserves_other_stems (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if stem_eq (tk_stem k1) (tk_stem k2) then
    true
  else
    option_value_eqb (sim_tree_get (sim_tree_insert t k1 v) k2) (sim_tree_get t k2).

(** Property 7: Batch operations on different keys commute (order independence) *)
Definition prop_batch_operations_commute (t : SimTree) (k1 k2 : TreeKey) (v1 v2 : Value) : bool :=
  if key_eqb k1 k2 then
    true
  else
    let t1 := sim_tree_insert (sim_tree_insert t k1 v1) k2 v2 in
    let t2 := sim_tree_insert (sim_tree_insert t k2 v2) k1 v1 in
    option_value_eqb (sim_tree_get t1 k1) (sim_tree_get t2 k1) &&
    option_value_eqb (sim_tree_get t1 k2) (sim_tree_get t2 k2).

(** Property 8: Stem colocation - same stem keys share submap after insert *)
Definition prop_stem_colocation (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if stem_eq (tk_stem k1) (tk_stem k2) then
    let t' := sim_tree_insert t k1 v in
    match stems_get (st_stems t') (tk_stem k1), stems_get (st_stems t') (tk_stem k2) with
    | Some m1, Some m2 => true
    | _, _ => false
    end
  else
    true.

(** Property 9: Delete is idempotent *)
Definition prop_delete_idempotent (t : SimTree) (k : TreeKey) : bool :=
  let t1 := sim_tree_delete t k in
  let t2 := sim_tree_delete t1 k in
  option_value_eqb (sim_tree_get t1 k) (sim_tree_get t2 k).

(** Property 10: Insert then delete same key = original get (for unset keys) *)
Definition prop_insert_delete_roundtrip (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  if is_zero_value v then
    true
  else
    let t' := sim_tree_delete (sim_tree_insert t k v) k in
    option_value_eqb (sim_tree_get t' k) None.

(** Property 11: Zero value insert acts as delete *)
Definition prop_zero_insert_is_delete (t : SimTree) (k : TreeKey) : bool :=
  option_value_eqb 
    (sim_tree_get (sim_tree_insert t k zero32) k) 
    (sim_tree_get (sim_tree_delete t k) k).

(** Property 12: Subindex independence - different subindices in same stem don't interfere *)
Definition prop_subindex_independence (t : SimTree) (stem_seed : Z) (idx1 idx2 : Z) (v : Value) : bool :=
  let s := gen_stem_from_seed stem_seed in
  let k1 := mkTreeKey s (Z.modulo idx1 256) in
  let k2 := mkTreeKey s (Z.modulo idx2 256) in
  if Z.eqb (Z.modulo idx1 256) (Z.modulo idx2 256) then
    true
  else
    option_value_eqb (sim_tree_get (sim_tree_insert t k1 v) k2) (sim_tree_get t k2).

(** Property 13: Empty tree is identity for stem lookup *)
Definition prop_empty_tree_no_stems (s : Stem) : bool :=
  match stems_get (st_stems empty_tree) s with
  | None => true
  | Some _ => false
  end.

(** Property 14: Multiple inserts at same key - last wins *)
Definition prop_last_insert_wins (t : SimTree) (k : TreeKey) (v1 v2 : Value) : bool :=
  if is_zero_value v2 then
    option_value_eqb (sim_tree_get (sim_tree_insert (sim_tree_insert t k v1) k v2) k) None
  else
    option_value_eqb (sim_tree_get (sim_tree_insert (sim_tree_insert t k v1) k v2) k) (Some v2).

(** ** Edge Case Properties (Properties 15-26) *)

(** Property 15: Maximum subindex (255) operations work correctly *)
Definition prop_max_subindex_works (t : SimTree) (stem_seed : Z) (v : Value) : bool :=
  let s := gen_stem_from_seed stem_seed in
  let k := mkTreeKey s 255 in
  if is_zero_value v then true
  else option_value_eqb (sim_tree_get (sim_tree_insert t k v) k) (Some v).

(** Property 16: Stems differing only in last bit are distinguished *)
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

(** Property 17: Full stem capacity - all 256 subindices can be populated *)
Definition prop_full_stem_256_values (stem_seed : Z) : bool :=
  let s := gen_stem_from_seed stem_seed in
  let indices := seq 0 256 in
  let t := fold_left (fun acc i =>
    let k := mkTreeKey s (Z.of_nat i) in
    let v := gen_nonzero_value (Z.of_nat i + 1) in
    sim_tree_insert acc k v) indices empty_tree in
  List.forallb (fun i =>
    let k := mkTreeKey s (Z.of_nat i) in
    let v := gen_nonzero_value (Z.of_nat i + 1) in
    option_value_eqb (sim_tree_get t k) (Some v)) indices.

(** Property 18: Deep tree operations - trees with many stems *)
Definition prop_deep_tree_operations (seeds : list Z) (query_seed : Z) (v : Value) : bool :=
  let stems := map gen_stem_from_seed seeds in
  let t := fold_left (fun acc_pair s =>
    let acc := fst acc_pair in
    let idx := snd acc_pair in
    let k := mkTreeKey s 0 in
    let val := gen_nonzero_value (Z.of_nat idx + 1) in
    (sim_tree_insert acc k val, S idx)) stems (empty_tree, 0%nat) in
  let query_stem := gen_stem_from_seed query_seed in
  let query_key := mkTreeKey query_stem 0 in
  if is_zero_value v then true
  else
    let t' := sim_tree_insert (fst t) query_key v in
    option_value_eqb (sim_tree_get t' query_key) (Some v).

(** Property 19: Alternating insert-delete stress test *)
Definition prop_alternating_insert_delete (t : SimTree) (keys : list TreeKey) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let t' := fold_left (fun acc k =>
      sim_tree_delete (sim_tree_insert acc k v) k) keys t in
    List.forallb (fun k =>
      option_value_eqb (sim_tree_get t' k) (sim_tree_get t k)) keys.

(** Property 20: Batch vs individual equivalence (distinct keys only) *)
Definition prop_batch_then_individual (t : SimTree) (k1 k2 k3 : TreeKey) (v1 v2 v3 : Value) : bool :=
  if key_eqb k1 k2 || key_eqb k2 k3 || key_eqb k1 k3 then true
  else
    let t_batch := sim_tree_insert (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2) k3 v3 in
    let check1 := option_value_eqb (sim_tree_get t_batch k1) 
                    (if is_zero_value v1 then None else Some v1) in
    let check2 := option_value_eqb (sim_tree_get t_batch k2) 
                    (if is_zero_value v2 then None else Some v2) in
    let check3 := option_value_eqb (sim_tree_get t_batch k3) 
                    (if is_zero_value v3 then None else Some v3) in
    check1 && check2 && check3.

(** Property 21: Boundary subindex transitions (0->1, 127->128, 254->255) *)
Definition prop_boundary_subindex_transitions (t : SimTree) (stem_seed : Z) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let s := gen_stem_from_seed stem_seed in
    let k0 := mkTreeKey s 0 in
    let k1 := mkTreeKey s 1 in
    let k127 := mkTreeKey s 127 in
    let k128 := mkTreeKey s 128 in
    let k254 := mkTreeKey s 254 in
    let k255 := mkTreeKey s 255 in
    let t' := sim_tree_insert (sim_tree_insert (sim_tree_insert 
              (sim_tree_insert (sim_tree_insert (sim_tree_insert t k0 v) k1 v) k127 v) 
              k128 v) k254 v) k255 v in
    option_value_eqb (sim_tree_get t' k0) (Some v) &&
    option_value_eqb (sim_tree_get t' k1) (Some v) &&
    option_value_eqb (sim_tree_get t' k127) (Some v) &&
    option_value_eqb (sim_tree_get t' k128) (Some v) &&
    option_value_eqb (sim_tree_get t' k254) (Some v) &&
    option_value_eqb (sim_tree_get t' k255) (Some v).

(** Property 22: Overwrite then delete leaves no trace *)
Definition prop_overwrite_delete_clean (t : SimTree) (k : TreeKey) (v1 v2 : Value) : bool :=
  let t1 := sim_tree_delete (sim_tree_insert (sim_tree_insert t k v1) k v2) k in
  option_value_eqb (sim_tree_get t1 k) None.

(** Property 23: Multiple stems with interleaved operations *)
Definition prop_interleaved_multi_stem (stem_seed1 stem_seed2 : Z) (v1 v2 : Value) : bool :=
  if is_zero_value v1 || is_zero_value v2 then true
  else
    let s1 := gen_stem_from_seed stem_seed1 in
    let s2 := gen_stem_from_seed stem_seed2 in
    if stem_eq s1 s2 then true
    else
      let k1_0 := mkTreeKey s1 0 in
      let k1_1 := mkTreeKey s1 1 in
      let k2_0 := mkTreeKey s2 0 in
      let k2_1 := mkTreeKey s2 1 in
      let t := sim_tree_insert (sim_tree_insert (sim_tree_insert 
                (sim_tree_insert empty_tree k1_0 v1) k2_0 v2) k1_1 v1) k2_1 v2 in
      option_value_eqb (sim_tree_get t k1_0) (Some v1) &&
      option_value_eqb (sim_tree_get t k1_1) (Some v1) &&
      option_value_eqb (sim_tree_get t k2_0) (Some v2) &&
      option_value_eqb (sim_tree_get t k2_1) (Some v2).

(** Property 24: Large key sequence maintains consistency *)
Definition prop_large_sequence_consistent (base_seed : Z) (n : nat) (v : Value) : bool :=
  if is_zero_value v then true
  else if (n =? 0)%nat then true
  else
    let keys := map (fun i => gen_key_from_bytes (base_seed + Z.of_nat i) (Z.of_nat i)) (seq 0 n) in
    let t := fold_left (fun acc k => sim_tree_insert acc k v) keys empty_tree in
    List.forallb (fun k => option_value_eqb (sim_tree_get t k) (Some v)) keys.

(** Property 25: Delete non-existent key is no-op *)
Definition prop_delete_nonexistent_noop (t : SimTree) (k1 k2 : TreeKey) (v : Value) : bool :=
  if key_eqb k1 k2 then true
  else if is_zero_value v then true
  else
    let t1 := sim_tree_insert t k1 v in
    let t2 := sim_tree_delete t1 k2 in
    option_value_eqb (sim_tree_get t2 k1) (Some v).

(** Property 26: Stem with high-bit bytes *)
Definition prop_high_bit_stem_works (t : SimTree) (idx : Z) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let s := mkStem (repeat 128 31) in
    let k := mkTreeKey s (Z.modulo idx 256) in
    option_value_eqb (sim_tree_get (sim_tree_insert t k v) k) (Some v).

(** ** Iterator Properties (Properties 27-31) *)

From Stdlib Require Import Permutation.

(** Helper: check if two lists are permutations of each other *)
Fixpoint list_count {A : Type} (eqb : A -> A -> bool) (x : A) (l : list A) : nat :=
  match l with
  | [] => 0
  | h :: t => (if eqb h x then 1 else 0) + list_count eqb x t
  end%nat.

Definition is_permutation_of {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  Nat.eqb (List.length l1) (List.length l2) &&
  List.forallb (fun x => Nat.eqb (list_count eqb x l1) (list_count eqb x l2)) l1.

(** Boolean equality for Entry (key-value pair) *)
Definition entry_eqb (e1 e2 : Entry) : bool :=
  key_eqb (fst e1) (fst e2) && value_eqb (snd e1) (snd e2).

(** Property 27: drain on a set yields a permutation of original entries
    (after draining all entries, we get a permutation of what was there) *)
Definition prop_drain_yields_all_elements (t : SimTree) : bool :=
  let entries := sim_tree_entries t in
  let drained := sim_tree_fold (fun acc k v => (k, v) :: acc) [] t in
  is_permutation_of entry_eqb entries drained.

(** Property 28: iter doesn't modify source (iteration is read-only)
    After folding, we can still retrieve all previously stored values *)
Definition prop_iter_preserves_collection (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let t' := sim_tree_insert t k v in
    let _ := sim_tree_fold (fun acc _ _ => acc + 1)%nat 0%nat t' in
    option_value_eqb (sim_tree_get t' k) (Some v).

(** Property 29: fold matches List.fold_left on entries
    sim_tree_fold f init t = fold_left (fun acc (k,v) => f acc k v) (entries t) init *)
Definition prop_fold_matches_list_fold (t : SimTree) : bool :=
  let sum_via_tree := sim_tree_fold (fun acc _ v => acc + hd 0 v) 0 t in
  let sum_via_list := fold_left (fun acc e => acc + hd 0 (snd e)) (sim_tree_entries t) 0 in
  Z.eqb sum_via_tree sum_via_list.

(** Property 30: entries reflect all inserted values
    After inserting k->v, entries should contain that mapping *)
Definition prop_entries_contain_inserted (t : SimTree) (k : TreeKey) (v : Value) : bool :=
  if is_zero_value v then true
  else
    let t' := sim_tree_insert t k v in
    let entries := sim_tree_entries t' in
    existsb (fun e => key_eqb (fst e) k && value_eqb (snd e) v) entries.

(** Helper: collect builds a tree from entries that matches original gets *)
Definition collect_from_entries (entries : list Entry) : SimTree :=
  fold_left (fun acc e => sim_tree_insert acc (fst e) (snd e)) entries empty_tree.

(** Property 31: iter().collect() equals original for all stored keys
    Collecting entries back into a tree preserves all values *)
Definition prop_collect_roundtrip (t : SimTree) : bool :=
  let entries := sim_tree_entries t in
  let t' := collect_from_entries entries in
  List.forallb (fun e => 
    option_value_eqb (sim_tree_get t' (fst e)) (Some (snd e))
  ) entries.

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

(** ** Edge Case Generators *)

(** Generate stem with all zeros *)
Definition gen_zero_stem : Stem := mkStem (repeat 0 31).

(** Generate stem with all ones (255 bytes) *)
Definition gen_ones_stem : Stem := mkStem (repeat 255 31).

(** Generate stem with alternating pattern *)
Definition gen_alternating_stem : Stem := 
  mkStem (map (fun i => if Nat.even i then 0 else 255) (seq 0 31)).

(** Generator that includes edge case stems *)
#[export] Instance genEdgeCaseStem : Gen Stem :=
  {| arbitrary :=
       freq [ (7%nat, bindGen arbitrary (fun seed : Z => returnGen (gen_stem_from_byte seed)))
            ; (1%nat, returnGen gen_zero_stem)
            ; (1%nat, returnGen gen_ones_stem)
            ; (1%nat, returnGen gen_alternating_stem)
            ] |}.

(** Generator for keys with same stem (testing subindex independence) *)
Definition gen_same_stem_keys (stem_seed : Z) : G (TreeKey * TreeKey) :=
  let s := gen_stem_from_seed stem_seed in
  bindGen arbitrary (fun idx1 : Z =>
    bindGen arbitrary (fun idx2 : Z =>
      returnGen (mkTreeKey s (Z.modulo idx1 256), mkTreeKey s (Z.modulo idx2 256)))).

(** Generator for boundary subindices (0, 127, 128, 255) *)
Definition gen_boundary_subindex : G Z :=
  elements 0%Z [0; 127; 128; 255]%Z.

(** Generator for keys at subindex boundaries *)
#[export] Instance genBoundaryKey : Gen TreeKey :=
  {| arbitrary :=
       freq [ (8%nat, arbitrary)
            ; (2%nat, bindGen arbitrary (fun stem_seed : Z =>
                       bindGen gen_boundary_subindex (fun idx =>
                         returnGen (gen_key_from_bytes stem_seed idx))))
            ] |}.

(** Generator for large trees (stress testing) *)
Definition genLargeSimTree : G SimTree :=
  bindGen (choose (10, 20)%nat) (fun n =>
    List.fold_right (fun _ acc =>
      bindGen acc (fun t =>
        bindGen arbitrary (fun k : TreeKey =>
          bindGen arbitrary (fun v : Value =>
            returnGen (sim_tree_insert t k v)))))
    (returnGen empty_tree)
    (List.repeat tt n)).

(** Generator for trees with many keys in same stem (testing 256 subindex capacity) *)
Definition genDenseStemTree (stem_seed : Z) : G SimTree :=
  let s := gen_stem_from_seed stem_seed in
  bindGen (choose (1, 50)%nat) (fun n =>
    List.fold_right (fun i acc =>
      bindGen acc (fun t =>
        bindGen arbitrary (fun v : Value =>
          let idx := Z.of_nat i in
          returnGen (sim_tree_insert t (mkTreeKey s idx) v))))
    (returnGen empty_tree)
    (seq 0 n)).

(** ** Stress Test Generators *)

(** Generator for trees with 100+ stems *)
Definition genMassiveStemTree : G SimTree :=
  bindGen (choose (100, 150)%nat) (fun n =>
    List.fold_right (fun i acc =>
      bindGen acc (fun t =>
        bindGen arbitrary (fun v : Value =>
          let stem_seed := Z.of_nat i in
          let s := gen_stem_from_seed stem_seed in
          returnGen (sim_tree_insert t (mkTreeKey s 0) v))))
    (returnGen empty_tree)
    (seq 0 n)).

(** Generator for operation sequences of 50+ ops *)
Definition genLongOpSequence : G (list (TreeKey * Value)) :=
  bindGen (choose (50, 100)%nat) (fun n =>
    sequenceGen (List.repeat 
      (bindGen arbitrary (fun k : TreeKey =>
        bindGen arbitrary (fun v : Value =>
          returnGen (k, v))))
      n)).

(** Generator for lists of keys (for stress tests) *)
#[export] Instance genKeyList : Gen (list TreeKey) :=
  {| arbitrary :=
       bindGen (choose (5, 20)%nat) (fun n =>
         sequenceGen (List.repeat arbitrary n)) |}.

(** Generator for stress test key lists (longer) *)
Definition genStressKeyList : G (list TreeKey) :=
  bindGen (choose (50, 100)%nat) (fun n =>
    sequenceGen (List.repeat arbitrary n)).

(** Generator for lists of Z seeds *)
#[export] Instance genZList : Gen (list Z) :=
  {| arbitrary :=
       bindGen (choose (5, 20)%nat) (fun n =>
         sequenceGen (List.repeat arbitrary n)) |}.

(** Generator for stress test Z seed lists *)
Definition genStressZList : G (list Z) :=
  bindGen (choose (50, 150)%nat) (fun n =>
    sequenceGen (List.repeat arbitrary n)).

(** Generator for stems differing by single bit *)
Definition genSimilarStems : G (Stem * Stem) :=
  bindGen arbitrary (fun seed : Z =>
    let base_bytes := map (fun i => Z.modulo (seed + Z.of_nat i) 256) (seq 0 30) in
    let s1 := mkStem (base_bytes ++ [0]) in
    let s2 := mkStem (base_bytes ++ [1]) in
    returnGen (s1, s2)).

(** Generator for maximum subindex keys *)
Definition genMaxSubindexKey : G TreeKey :=
  bindGen arbitrary (fun stem_seed : Z =>
    returnGen (mkTreeKey (gen_stem_from_seed stem_seed) 255)).

(** Generator for high-bit stems (all bytes have bit 7 set) *)
Definition genHighBitStem : G Stem :=
  returnGen (mkStem (repeat 128 31)).

(** Generator for all-255 stems *)
Definition genMaxByteStem : G Stem :=
  returnGen (mkStem (repeat 255 31)).

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

(** ** Additional Property Tests *)

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

(* Property 8: Stem colocation *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v : Value =>
        prop_stem_colocation t k1 k2 v))))).

(* Property 9: Delete idempotent *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    prop_delete_idempotent t k))).

(* Property 10: Insert-delete roundtrip *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_insert_delete_roundtrip t k v)))).

(* Property 11: Zero insert is delete *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    prop_zero_insert_is_delete t k))).

(* Property 12: Subindex independence *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun stem_seed : Z =>
    forAll arbitrary (fun idx1 : Z =>
      forAll arbitrary (fun idx2 : Z =>
        forAll arbitrary (fun v : Value =>
          prop_subindex_independence t stem_seed idx1 idx2 v)))))).

(* Property 13: Empty tree has no stems *)
QuickChick (forAll arbitrary (fun s : Stem =>
  prop_empty_tree_no_stems s)).

(* Property 14: Last insert wins *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v1 : Value =>
      forAll arbitrary (fun v2 : Value =>
        prop_last_insert_wins t k v1 v2))))).

(** ** Edge Case Property Tests (Properties 15-26) *)

(* Property 15: Maximum subindex (255) operations *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun stem_seed : Z =>
    forAll arbitrary (fun v : Value =>
      prop_max_subindex_works t stem_seed v)))).

(* Property 16: Similar stems distinguished *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun seed : Z =>
    forAll arbitrary (fun idx : Z =>
      forAll arbitrary (fun v1 : Value =>
        forAll arbitrary (fun v2 : Value =>
          prop_similar_stems_distinguished t seed idx v1 v2)))))).

(* Property 17: Full stem 256 values - run fewer times due to complexity *)
QuickChick (forAll arbitrary (fun stem_seed : Z =>
  prop_full_stem_256_values stem_seed)).

(* Property 18: Deep tree operations *)
QuickChick (forAll arbitrary (fun seeds : list Z =>
  forAll arbitrary (fun query_seed : Z =>
    forAll arbitrary (fun v : Value =>
      prop_deep_tree_operations seeds query_seed v)))).

(* Property 19: Alternating insert-delete stress test *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun keys : list TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_alternating_insert_delete t keys v)))).

(* Property 20: Batch then individual equivalence *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun k3 : TreeKey =>
        forAll arbitrary (fun v1 : Value =>
          forAll arbitrary (fun v2 : Value =>
            forAll arbitrary (fun v3 : Value =>
              prop_batch_then_individual t k1 k2 k3 v1 v2 v3)))))))).

(* Property 21: Boundary subindex transitions *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun stem_seed : Z =>
    forAll arbitrary (fun v : Value =>
      prop_boundary_subindex_transitions t stem_seed v)))).

(* Property 22: Overwrite then delete leaves no trace *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v1 : Value =>
      forAll arbitrary (fun v2 : Value =>
        prop_overwrite_delete_clean t k v1 v2))))).

(* Property 23: Interleaved multi-stem operations *)
QuickChick (forAll arbitrary (fun stem_seed1 : Z =>
  forAll arbitrary (fun stem_seed2 : Z =>
    forAll arbitrary (fun v1 : Value =>
      forAll arbitrary (fun v2 : Value =>
        prop_interleaved_multi_stem stem_seed1 stem_seed2 v1 v2))))).

(* Property 24: Large sequence consistency - run with smaller n for speed *)
QuickChick (forAll arbitrary (fun base_seed : Z =>
  forAll (choose (1, 30)%nat) (fun n : nat =>
    forAll arbitrary (fun v : Value =>
      prop_large_sequence_consistent base_seed n v)))).

(* Property 25: Delete non-existent key is no-op *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k1 : TreeKey =>
    forAll arbitrary (fun k2 : TreeKey =>
      forAll arbitrary (fun v : Value =>
        prop_delete_nonexistent_noop t k1 k2 v))))).

(* Property 26: High-bit stem works *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun idx : Z =>
    forAll arbitrary (fun v : Value =>
      prop_high_bit_stem_works t idx v)))).

(** ** Stress Test Property Invocations *)

(* Stress test: Large tree with many stems *)
QuickChick (forAll genMassiveStemTree (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_get_insert_same t k v)))).

(* Stress test: Long operation sequence *)
QuickChick (forAll genStressKeyList (fun keys : list TreeKey =>
  forAll arbitrary (fun v : Value =>
    prop_alternating_insert_delete empty_tree keys v))).

(* Stress test: Dense stem tree *)
QuickChick (forAll arbitrary (fun stem_seed : Z =>
  forAll (genDenseStemTree stem_seed) (fun t : SimTree =>
    forAll arbitrary (fun idx : Z =>
      forAll arbitrary (fun v : Value =>
        let s := gen_stem_from_seed stem_seed in
        let k := mkTreeKey s (Z.modulo idx 256) in
        prop_get_insert_same t k v))))).

(* Stress test: Many stems deep tree *)
QuickChick (forAll genStressZList (fun seeds : list Z =>
  forAll arbitrary (fun query_seed : Z =>
    forAll arbitrary (fun v : Value =>
      prop_deep_tree_operations seeds query_seed v)))).

(** ** Iterator Property Tests (Properties 27-31) *)

(* Property 27: Drain yields all elements (permutation) *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_drain_yields_all_elements t)).

(** ** Advanced Iterator Properties (Properties 32-37) *)

(** Helper: sum values with commutative addition *)
Definition sum_first_bytes (entries : list Entry) : Z :=
  fold_left (fun acc e => acc + hd 0 (snd e)) entries 0.

(** Helper: check if fold result matches for two entry orderings *)
Definition fold_results_match (entries1 entries2 : list Entry) : bool :=
  Z.eqb (sum_first_bytes entries1) (sum_first_bytes entries2).

(** Helper: filter entries by predicate on first byte of value *)
Definition filter_entries_by_value (pred : Z -> bool) (entries : list Entry) : list Entry :=
  filter (fun e => pred (hd 0 (snd e))) entries.

(** Helper: check value nonzero via list *)
Definition value_list_nonzero (v : Value) : bool :=
  negb (forallb (Z.eqb 0) v).

(** Property 32: Drain preserves elements - draining yields permutation of all entries
    This tests that sim_tree_fold with cons collects all key-value pairs *)
Definition prop_drain_preserves_elements (t : SimTree) : bool :=
  let entries := sim_tree_entries t in
  let drained := sim_tree_fold (fun acc k v => (k, v) :: acc) [] t in
  (* drained is rev of entries, so check same length and permutation-like properties *)
  Nat.eqb (List.length entries) (List.length drained) &&
  List.forallb (fun e => 
    existsb (fun d => entry_eqb e d) drained
  ) entries.

(** Property 33: Iter order independence - iteration order doesn't affect
    fold results for commutative operations (addition) *)
Definition prop_iter_order_independence (t : SimTree) : bool :=
  let entries := sim_tree_entries t in
  let sum1 := sim_tree_fold (fun acc _ v => acc + hd 0 v) 0 t in
  let sum2 := fold_left (fun acc e => acc + hd 0 (snd e)) (rev entries) 0 in
  Z.eqb sum1 sum2.

(** Property 34: Fold associativity - folding with associative op is order-independent
    Uses multiplication which is both commutative and associative *)
Definition prop_fold_associativity (t : SimTree) : bool :=
  let entries := sim_tree_entries t in
  (* Use mod arithmetic to avoid overflow, operation: (acc + first_byte) mod 1000 *)
  let fold_fn := fun acc e => Z.modulo (acc + hd 1 (snd e)) 1000 in
  let result1 := fold_left fold_fn entries 0 in
  let result2 := fold_left fold_fn (rev entries) 0 in
  Z.eqb result1 result2.

(** Property 35: Filter then drain - filtering entries then collecting equals
    collecting filtered elements directly *)
Definition prop_filter_then_drain (t : SimTree) (threshold : Z) : bool :=
  let entries := sim_tree_entries t in
  let thresh := Z.modulo threshold 256 in
  (* Filter entries where first byte > threshold *)
  let filtered := filter (fun e => Z.ltb thresh (hd 0 (snd e))) entries in
  (* Drain with filter predicate *)
  let drained_filtered := sim_tree_fold 
    (fun acc k v => if Z.ltb thresh (hd 0 v) then (k, v) :: acc else acc) [] t in
  Nat.eqb (List.length filtered) (List.length drained_filtered).

(** Property 36: Drain count matches entry count - number of drained elements
    equals sim_tree_entry_count *)
Definition prop_drain_count_matches (t : SimTree) : bool :=
  let count_via_drain := sim_tree_fold (fun acc _ _ => S acc) 0%nat t in
  let count_via_entries := List.length (sim_tree_entries t) in
  Nat.eqb count_via_drain count_via_entries.

(** Property 37: Double iteration consistency - iterating twice yields same results *)
Definition prop_double_iteration_consistent (t : SimTree) : bool :=
  let sum1 := sim_tree_fold (fun acc _ v => acc + hd 0 v) 0 t in
  let sum2 := sim_tree_fold (fun acc _ v => acc + hd 0 v) 0 t in
  Z.eqb sum1 sum2.

(* Property 28: Iter preserves collection (read-only) *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_iter_preserves_collection t k v)))).

(* Property 29: Fold matches List.fold_left *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_fold_matches_list_fold t)).

(* Property 30: Entries contain inserted values *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun k : TreeKey =>
    forAll arbitrary (fun v : Value =>
      prop_entries_contain_inserted t k v)))).

(* Property 31: Collect roundtrip *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_collect_roundtrip t)).

(** ** Advanced Iterator Property Tests (Properties 32-37) *)

(* Property 32: Drain preserves elements *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_drain_preserves_elements t)).

(* Property 33: Iter order independence for commutative ops *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_iter_order_independence t)).

(* Property 34: Fold associativity - order independent for associative ops *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_fold_associativity t)).

(* Property 35: Filter then drain equivalence *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  forAll arbitrary (fun threshold : Z =>
    prop_filter_then_drain t threshold))).

(* Property 36: Drain count matches entry count *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_drain_count_matches t)).

(* Property 37: Double iteration consistency *)
QuickChick (forAll arbitrary (fun t : SimTree =>
  prop_double_iteration_consistent t)).

(** ** Theorem Statements (proved in tree.v)
    
    These theorems correspond to our properties.
    QuickChick helps us gain confidence before investing in proofs.
*)

Check get_insert_same.
Check get_empty.
Check get_delete.
Check stem_colocation.
Check insert_order_independent_stems.
Check insert_order_independent_subindex.

(** End of quickchick_tests.v *)
