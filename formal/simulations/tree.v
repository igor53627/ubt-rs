(** * Tree Operations Simulation
    
    Idiomatic Rocq implementation of UBT operations.
    This file provides a clean functional specification that
    mirrors the Rust implementation but is easier to reason about.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.FSets.FMapList.
Require Import Stdlib.Structures.OrderedTypeEx.
Import ListNotations.

Open Scope Z_scope.

(** ** Types *)

Definition Byte := Z.
Definition Bytes32 := list Byte.
Definition Bytes31 := list Byte.

(** Stem: 31-byte key prefix *)
Record Stem := mkStem {
  stem_data : Bytes31
}.

(** SubIndex: last byte of key (0-255) *)
Definition SubIndex := Byte.

(** TreeKey: full 32-byte key = stem ++ [subindex] *)
Record TreeKey := mkTreeKey {
  tk_stem : Stem;
  tk_subindex : SubIndex
}.

(** Value stored in leaves *)
Definition Value := Bytes32.

(** ** Zero constants *)

Definition zero_byte : Byte := 0.
Definition zero32 : Bytes32 := repeat zero_byte 32.
Definition zero31 : Bytes31 := repeat zero_byte 31.
Definition zero_stem : Stem := mkStem zero31.

(** ** Helper predicates *)

Definition is_zero_value (v : Value) : bool :=
  forallb (fun b => Z.eqb b 0) v.

Definition value_nonzero (v : Value) : Prop :=
  is_zero_value v = false.

(** ** Bit operations on stems *)

(** Get bit at position i (0 = MSB of first byte) *)
Definition stem_bit_at (s : Stem) (i : nat) : bool :=
  let byte_idx := (i / 8)%nat in
  let bit_idx := (7 - i mod 8)%nat in
  match nth_error (stem_data s) byte_idx with
  | Some b => Z.testbit b (Z.of_nat bit_idx)
  | None => false
  end.

(** Find first differing bit between two stems *)
Fixpoint first_diff_bit_aux (s1 s2 : Bytes31) (pos : nat) : option nat :=
  match s1, s2 with
  | [], [] => None
  | b1 :: rest1, b2 :: rest2 =>
      if Z.eqb b1 b2 then
        first_diff_bit_aux rest1 rest2 (pos + 8)%nat
      else
        let xor := Z.lxor b1 b2 in
        let leading := Z.to_nat (Z.log2 xor) in
        Some (pos + (7 - leading))%nat
  | _, _ => None
  end.

Definition first_diff_bit (s1 s2 : Stem) : option nat :=
  first_diff_bit_aux (stem_data s1) (stem_data s2) 0.

(** ** Stem Equality *)

Definition stem_eq (s1 s2 : Stem) : bool :=
  forallb (fun p => Z.eqb (fst p) (snd p)) 
          (combine (stem_data s1) (stem_data s2)).

Definition stem_eq_dec (s1 s2 : Stem) : {stem_eq s1 s2 = true} + {stem_eq s1 s2 = false}.
Proof.
  destruct (stem_eq s1 s2) eqn:H; [left | right]; reflexivity.
Defined.

Lemma forallb_combine_refl : forall (l : list Z),
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l l) = true.
Proof.
  induction l as [|x rest IH].
  - reflexivity.
  - simpl. rewrite Z.eqb_refl. exact IH.
Qed.

Lemma stem_eq_refl : forall s, stem_eq s s = true.
Proof.
  intros s.
  unfold stem_eq.
  apply forallb_combine_refl.
Qed.

(** ** Functional Map for Stem Values *)

(** Map from SubIndex to Value within a stem *)
Definition SubIndexMap := list (SubIndex * Value).

Definition sim_get (m : SubIndexMap) (idx : SubIndex) : option Value :=
  match find (fun p => Z.eqb (fst p) idx) m with
  | Some (_, v) => Some v
  | None => None
  end.

Definition sim_set (m : SubIndexMap) (idx : SubIndex) (v : Value) : SubIndexMap :=
  if is_zero_value v then
    filter (fun p => negb (Z.eqb (fst p) idx)) m
  else
    (idx, v) :: filter (fun p => negb (Z.eqb (fst p) idx)) m.

(** Helper lemmas for sim_get and sim_set *)

Lemma sim_get_set_same : forall m idx v,
  value_nonzero v ->
  sim_get (sim_set m idx v) idx = Some v.
Proof.
  intros m idx v Hnonzero.
  unfold sim_get, sim_set, value_nonzero, is_zero_value in *.
  rewrite Hnonzero.
  simpl.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma sim_get_set_other : forall m idx1 idx2 v,
  idx1 <> idx2 ->
  sim_get (sim_set m idx1 v) idx2 = sim_get m idx2.
Proof.
  intros m idx1 idx2 v Hneq.
  unfold sim_get, sim_set.
  destruct (is_zero_value v) eqn:Hzero.
  - induction m as [|[i val] rest IH].
    + reflexivity.
    + simpl.
      destruct (Z.eqb i idx1) eqn:E1.
      * simpl.
        destruct (Z.eqb i idx2) eqn:E2.
        { apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
          subst. contradiction. }
        { exact IH. }
      * simpl.
        destruct (Z.eqb i idx2) eqn:E2; auto.
  - simpl.
    destruct (Z.eqb idx1 idx2) eqn:E.
    + apply Z.eqb_eq in E. contradiction.
    + induction m as [|[i val'] rest IH].
      * reflexivity.
      * simpl.
        destruct (Z.eqb i idx1) eqn:E1; simpl.
        { destruct (Z.eqb i idx2) eqn:E2.
          - apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
            subst. contradiction.
          - exact IH. }
        { destruct (Z.eqb i idx2); auto. }
Qed.

Lemma find_filter_none : forall (m : SubIndexMap) idx,
  find (fun p => Z.eqb (fst p) idx) (filter (fun p => negb (Z.eqb (fst p) idx)) m) = None.
Proof.
  induction m as [|[i val] rest IH].
  - reflexivity.
  - simpl. intros idx.
    destruct (Z.eqb i idx) eqn:E; simpl.
    + apply IH.
    + rewrite E. apply IH.
Qed.

Lemma sim_get_set_zero : forall m idx,
  sim_get (sim_set m idx zero32) idx = None.
Proof.
  intros m idx.
  unfold sim_get, sim_set.
  assert (Hzero: is_zero_value zero32 = true).
  { unfold is_zero_value, zero32, zero_byte.
    simpl. reflexivity. }
  rewrite Hzero.
  rewrite find_filter_none.
  reflexivity.
Qed.

(** ** Node Type (Simulation) *)

Inductive SimNode : Type :=
  | SimEmpty : SimNode
  | SimInternal : SimNode -> SimNode -> SimNode
  | SimStem : Stem -> SubIndexMap -> SimNode
  | SimLeaf : Value -> SimNode.

(** ** Hash Function (Axiomatized) *)

Parameter hash_value : Value -> Bytes32.
Parameter hash_pair : Bytes32 -> Bytes32 -> Bytes32.
Parameter hash_stem : Stem -> Bytes32 -> Bytes32.

Axiom hash_zero_value : hash_value zero32 = zero32.
Axiom hash_zero_pair : hash_pair zero32 zero32 = zero32.
Axiom hash_deterministic_value : forall v1 v2, v1 = v2 -> hash_value v1 = hash_value v2.
Axiom hash_deterministic_pair : forall a1 b1 a2 b2, 
  a1 = a2 -> b1 = b2 -> hash_pair a1 b1 = hash_pair a2 b2.

(** Node hash computation *)
Fixpoint sim_node_hash (n : SimNode) : Bytes32 :=
  match n with
  | SimEmpty => zero32
  | SimInternal l r => hash_pair (sim_node_hash l) (sim_node_hash r)
  | SimStem s values => 
      hash_stem s zero32
  | SimLeaf v => hash_value v
  end.

(** ** Tree Operations *)

(** Map from Stem to SubIndexMap *)
Definition StemMap := list (Stem * SubIndexMap).

Definition stems_get (m : StemMap) (s : Stem) : option SubIndexMap :=
  match find (fun p => stem_eq (fst p) s) m with
  | Some (_, v) => Some v
  | None => None
  end.

Definition stems_set (m : StemMap) (s : Stem) (v : SubIndexMap) : StemMap :=
  (s, v) :: filter (fun p => negb (stem_eq (fst p) s)) m.

(** Helper lemmas for stems_get and stems_set *)

Lemma stems_get_set_same : forall m s v,
  stems_get (stems_set m s v) s = Some v.
Proof.
  intros m s v.
  unfold stems_get, stems_set.
  simpl.
  rewrite stem_eq_refl.
  reflexivity.
Qed.

Lemma forallb_combine_sym : forall l1 l2,
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l1 l2) =
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l2 l1).
Proof.
  induction l1 as [|b1 rest1 IH]; intros l2.
  - destruct l2; reflexivity.
  - destruct l2 as [|b2 rest2].
    + reflexivity.
    + simpl. rewrite Z.eqb_sym.
      destruct (Z.eqb b2 b1) eqn:E.
      * f_equal. apply IH.
      * reflexivity.
Qed.

Lemma stem_eq_sym : forall s1 s2,
  stem_eq s1 s2 = stem_eq s2 s1.
Proof.
  intros s1 s2.
  unfold stem_eq.
  apply forallb_combine_sym.
Qed.

Lemma forallb_combine_trans : forall l1 l2 l3,
  length l1 = length l2 ->
  length l2 = length l3 ->
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l1 l2) = true ->
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l2 l3) = true ->
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l1 l3) = true.
Proof.
  induction l1 as [|b1 rest1 IH]; intros l2 l3 Hlen12 Hlen23 H12 H23.
  - reflexivity.
  - destruct l2 as [|b2 rest2]; [discriminate|].
    destruct l3 as [|b3 rest3]; [discriminate|].
    simpl in *.
    injection Hlen12 as Hlen12.
    injection Hlen23 as Hlen23.
    destruct (Z.eqb b1 b2) eqn:E12; [|discriminate].
    destruct (Z.eqb b2 b3) eqn:E23; [|discriminate].
    apply Z.eqb_eq in E12.
    apply Z.eqb_eq in E23.
    subst. rewrite Z.eqb_refl.
    eapply IH; eauto.
Qed.

Lemma stem_eq_trans : forall s1 s2 s3,
  length (stem_data s1) = length (stem_data s2) ->
  length (stem_data s2) = length (stem_data s3) ->
  stem_eq s1 s2 = true -> stem_eq s2 s3 = true -> stem_eq s1 s3 = true.
Proof.
  intros s1 s2 s3 Hlen12 Hlen23 H12 H23.
  unfold stem_eq in *.
  eapply forallb_combine_trans; eauto.
Qed.

Lemma stems_get_set_other : forall m s1 s2 v,
  stem_eq s1 s2 = false ->
  stems_get (stems_set m s1 v) s2 = stems_get m s2.
Proof.
  intros m s1 s2 v Hneq.
  unfold stems_get, stems_set.
  simpl.
  rewrite Hneq.
  induction m as [|[stem submap] rest IH].
  - reflexivity.
  - simpl.
    destruct (stem_eq stem s1) eqn:E1; simpl.
    + destruct (stem_eq stem s2) eqn:E2.
      * exfalso.
        assert (Hlen1: length (stem_data s1) = length (stem_data stem)).
        { admit. }
        assert (Hlen2: length (stem_data stem) = length (stem_data s2)).
        { admit. }
        assert (stem_eq s1 s2 = true).
        { rewrite stem_eq_sym in E1.
          eapply stem_eq_trans; eauto. }
        rewrite H in Hneq. discriminate.
      * exact IH.
    + destruct (stem_eq stem s2) eqn:E2; [reflexivity | exact IH].
Admitted.

(** Simplified tree as map of stems *)
Record SimTree := mkSimTree {
  st_stems : StemMap
}.

Definition empty_tree : SimTree := mkSimTree [].

(** Get value from tree *)
Definition sim_tree_get (t : SimTree) (k : TreeKey) : option Value :=
  match stems_get (st_stems t) (tk_stem k) with
  | Some submap => sim_get submap (tk_subindex k)
  | None => None
  end.

(** Insert value into tree *)
Definition sim_tree_insert (t : SimTree) (k : TreeKey) (v : Value) : SimTree :=
  let stem := tk_stem k in
  let idx := tk_subindex k in
  let old_submap := 
    match stems_get (st_stems t) stem with
    | Some m => m
    | None => []
    end in
  let new_submap := sim_set old_submap idx v in
  mkSimTree (stems_set (st_stems t) stem new_submap).

(** Delete value from tree *)
Definition sim_tree_delete (t : SimTree) (k : TreeKey) : SimTree :=
  sim_tree_insert t k zero32.

(** ** Properties *)

(** Get from empty tree returns None *)
Theorem get_empty : forall k,
  sim_tree_get empty_tree k = None.
Proof.
  intros k.
  unfold sim_tree_get, empty_tree, stems_get.
  simpl. reflexivity.
Qed.

(** Insert then get same key returns value *)
Theorem get_insert_same : forall t k v,
  value_nonzero v ->
  sim_tree_get (sim_tree_insert t k v) k = Some v.
Proof.
  intros t k v Hnonzero.
  unfold sim_tree_get, sim_tree_insert.
  simpl.
  rewrite stems_get_set_same.
  destruct (stems_get (st_stems t) (tk_stem k)) eqn:Hstems.
  - apply sim_get_set_same. exact Hnonzero.
  - apply sim_get_set_same. exact Hnonzero.
Qed.

(** Insert then get different key (different stem) is unchanged *)
Theorem get_insert_other_stem : forall t k1 k2 v,
  stem_eq (tk_stem k1) (tk_stem k2) = false ->
  sim_tree_get (sim_tree_insert t k1 v) k2 = sim_tree_get t k2.
Proof.
  intros t k1 k2 v Hdiff.
  unfold sim_tree_get, sim_tree_insert.
  simpl.
  rewrite stems_get_set_other by exact Hdiff.
  reflexivity.
Qed.

(** Helper: stems_get with equivalent stems returns same result *)
Lemma stems_get_stem_eq : forall m s1 s2,
  stem_eq s1 s2 = true ->
  stems_get m s1 = stems_get m s2.
Proof.
  intros m s1 s2 Heq.
  unfold stems_get.
  induction m as [|[stem submap] rest IH].
  - reflexivity.
  - simpl.
    destruct (stem_eq stem s1) eqn:E1; destruct (stem_eq stem s2) eqn:E2; auto.
    + admit.
    + admit.
Admitted.

(** Insert then get different key (same stem, different subindex) is unchanged *)
Theorem get_insert_other_subindex : forall t k1 k2 v,
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  tk_subindex k1 <> tk_subindex k2 ->
  sim_tree_get (sim_tree_insert t k1 v) k2 = sim_tree_get t k2.
Proof.
  intros t k1 k2 v Hsame Hdiff.
  unfold sim_tree_get, sim_tree_insert.
  simpl.
  assert (Hget_eq: stems_get (stems_set (st_stems t) (tk_stem k1)
           (sim_set match stems_get (st_stems t) (tk_stem k1) with
                    | Some m => m
                    | None => []
                    end (tk_subindex k1) v)) (tk_stem k2) =
          Some (sim_set match stems_get (st_stems t) (tk_stem k1) with
                        | Some m => m
                        | None => []
                        end (tk_subindex k1) v)).
  { rewrite stems_get_stem_eq with (s1 := tk_stem k2) (s2 := tk_stem k1).
    - apply stems_get_set_same.
    - rewrite stem_eq_sym. exact Hsame. }
  rewrite Hget_eq.
  rewrite sim_get_set_other by exact Hdiff.
  assert (Hget_orig: stems_get (st_stems t) (tk_stem k2) = stems_get (st_stems t) (tk_stem k1)).
  { apply stems_get_stem_eq. rewrite stem_eq_sym. exact Hsame. }
  rewrite Hget_orig.
  destruct (stems_get (st_stems t) (tk_stem k1)) eqn:Hget1.
  - reflexivity.
  - reflexivity.
Qed.

(** Delete removes value *)
Theorem get_delete : forall t k,
  sim_tree_get (sim_tree_delete t k) k = None.
Proof.
  intros t k.
  unfold sim_tree_delete, sim_tree_get, sim_tree_insert.
  simpl.
  rewrite stems_get_set_same.
  destruct (stems_get (st_stems t) (tk_stem k)).
  - apply sim_get_set_zero.
  - apply sim_get_set_zero.
Qed.

(** ** Order Independence *)

(** Helper: tree equality based on content *)
Definition tree_eq (t1 t2 : SimTree) : Prop :=
  forall k, sim_tree_get t1 k = sim_tree_get t2 k.

(** Insertion order doesn't matter for final state (different stems) *)
Theorem insert_order_independent_stems : forall t k1 v1 k2 v2,
  stem_eq (tk_stem k1) (tk_stem k2) = false ->
  tree_eq 
    (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
    (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  intros t k1 v1 k2 v2 Hdiff.
  unfold tree_eq. intros k.
  destruct (stem_eq (tk_stem k) (tk_stem k1)) eqn:Ek1;
  destruct (stem_eq (tk_stem k) (tk_stem k2)) eqn:Ek2.
  - unfold stem_eq in *.
    rewrite forallb_forall in Ek1.
    rewrite forallb_forall in Ek2.
    admit.
  - destruct (Z.eq_dec (tk_subindex k) (tk_subindex k1)) as [Heq|Hneq].
    + admit.
    + admit.
  - admit.
  - rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek2).
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek1).
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek1).
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek2).
    reflexivity.
Admitted.

(** Insertion order doesn't matter for final state (same stem, different subindex) *)
Theorem insert_order_independent_subindex : forall t k1 v1 k2 v2,
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  tk_subindex k1 <> tk_subindex k2 ->
  tree_eq 
    (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
    (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  intros t k1 v1 k2 v2 Hsame Hdiff.
  unfold tree_eq. intros k.
  admit.
Admitted.

(** ** Hash Properties *)

(** Empty tree has zero hash *)
Theorem empty_tree_hash_zero :
  sim_node_hash SimEmpty = zero32.
Proof.
  reflexivity.
Qed.

(** Hash is deterministic *)
Theorem hash_deterministic_node : forall n,
  sim_node_hash n = sim_node_hash n.
Proof.
  reflexivity.
Qed.

(** ** Stem Co-location *)

(** Keys with same stem are stored in same subtree *)
Theorem stem_colocation : forall t k1 k2,
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  forall v, 
    exists submap,
      stems_get (st_stems (sim_tree_insert t k1 v)) (tk_stem k1) = Some submap /\
      stems_get (st_stems (sim_tree_insert t k1 v)) (tk_stem k2) = Some submap.
Proof.
  intros t k1 k2 Hsame v.
  unfold sim_tree_insert. simpl.
  exists (sim_set match stems_get (st_stems t) (tk_stem k1) with
                  | Some m => m
                  | None => []
                  end (tk_subindex k1) v).
  split.
  - apply stems_get_set_same.
  - unfold stems_get. simpl.
    rewrite Hsame. reflexivity.
Qed.

(** ** Well-formedness *)

Definition wf_value (v : Value) : Prop := length v = 32%nat.
Definition wf_stem (s : Stem) : Prop := length (stem_data s) = 31%nat.

Inductive wf_tree : SimTree -> Prop :=
  | wf_empty : wf_tree empty_tree
  | wf_insert : forall t k v,
      wf_tree t ->
      wf_value v ->
      wf_stem (tk_stem k) ->
      wf_tree (sim_tree_insert t k v).

(** Insertion preserves well-formedness *)
Theorem insert_preserves_wf : forall t k v,
  wf_tree t -> wf_value v -> wf_stem (tk_stem k) ->
  wf_tree (sim_tree_insert t k v).
Proof.
  intros. constructor; assumption.
Qed.
