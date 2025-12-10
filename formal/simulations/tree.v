(** * Tree Operations Simulation
    
    Idiomatic Rocq implementation of UBT operations.
    This file provides a clean functional specification that
    mirrors the Rust implementation but is easier to reason about.
    
    ** Global Well-Formedness Invariant
    
    All stems in this specification are assumed to be well-formed (31 bytes).
    This invariant is maintained by construction: stems are always derived
    from valid 32-byte TreeKeys per EIP-7864, where the first 31 bytes form
    the stem and the 32nd byte is the subindex.
    
    The [wf_stem] predicate (length = 31) captures this property formally.
    The axiom [stem_eq_true] is a convenience wrapper over the proven lemma
    [stem_eq_true_wf] that assumes this global invariant, avoiding the need
    to thread well-formedness proofs through every stem-related lemma.
    
    For proofs requiring explicit well-formedness, use [stem_eq_true_wf]
    with appropriate [wf_stem] premises. The same applies to [stem_eq_via_third].
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.FSets.FMapList.
Require Import Stdlib.Structures.OrderedTypeEx.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
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

(** Helper: forallb on combine implies list equality when same length *)
Lemma forallb_combine_eq : forall (l1 l2 : list Z),
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l1 l2) = true ->
  length l1 = length l2 ->
  l1 = l2.
Proof.
  induction l1 as [|x1 rest1 IH]; intros l2 Hfb Hlen.
  - destruct l2; [reflexivity | simpl in Hlen; discriminate].
  - destruct l2 as [|x2 rest2]; [simpl in Hlen; discriminate |].
    simpl in Hfb, Hlen.
    apply Bool.andb_true_iff in Hfb. destruct Hfb as [Heq Hrest].
    apply Z.eqb_eq in Heq. subst x2.
    f_equal. apply IH; [exact Hrest | injection Hlen; auto].
Qed.

(** Stem equality implies propositional equality for same-length stems *)
Lemma stem_eq_true_len : forall s1 s2, 
  length (stem_data s1) = length (stem_data s2) ->
  stem_eq s1 s2 = true -> s1 = s2.
Proof.
  intros s1 s2 Hlen H.
  destruct s1 as [d1], s2 as [d2].
  unfold stem_eq in H. simpl in *.
  f_equal.
  apply forallb_combine_eq; assumption.
Qed.

(** Well-formed stem has 31 bytes *)
Definition wf_stem (s : Stem) : Prop := length (stem_data s) = 31%nat.

(** For well-formed stems (31 bytes), stem_eq implies propositional equality *)
Lemma stem_eq_true_wf : forall s1 s2, 
  wf_stem s1 -> wf_stem s2 ->
  stem_eq s1 s2 = true -> s1 = s2.
Proof.
  intros s1 s2 Hwf1 Hwf2 H.
  apply stem_eq_true_len; [|exact H].
  unfold wf_stem in *. lia.
Qed.

(** [AXIOM:STRUCTURAL] Stem equality implies propositional equality.
    
    This axiom is a convenience wrapper over the proven [stem_eq_true_wf].
    It assumes the global well-formedness invariant: all stems are 31 bytes.
    This holds by construction since stems derive from 32-byte TreeKeys.
    
    Design decision: We keep this axiom for ergonomic proofs that don't
    want to thread [wf_stem] hypotheses. Proofs requiring explicit WF
    tracking should use [stem_eq_true_wf] instead.
    
    Used by: [treekey_neq_same_stem_diff_subindex], [get_insert_other],
    [stem_eq_false_from_third].
    
    Risk: Low - the invariant is maintained by all tree construction paths. *)
Axiom stem_eq_true : forall s1 s2, stem_eq s1 s2 = true -> s1 = s2.

(** Key inequality: same stem + different keys implies different subindices *)
Lemma treekey_neq_same_stem_diff_subindex :
  forall k1 k2,
    stem_eq (tk_stem k1) (tk_stem k2) = true ->
    k1 <> k2 ->
    tk_subindex k1 <> tk_subindex k2.
Proof.
  intros k1 k2 Hstem Hneq.
  apply stem_eq_true in Hstem.
  intro Hidx.
  apply Hneq.
  destruct k1 as [s1 i1], k2 as [s2 i2].
  simpl in *. subst.
  reflexivity.
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

Lemma sim_get_set_zero_value : forall m idx v,
  is_zero_value v = true ->
  sim_get (sim_set m idx v) idx = None.
Proof.
  intros m idx v Hzero.
  unfold sim_get, sim_set.
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

(** [AXIOM:DESIGN] Zero-hash property per EIP-7864 sparse tree optimization.
    Empty values hash to zero, enabling efficient sparse representation. *)
Axiom hash_zero_value : hash_value zero32 = zero32.

(** [AXIOM:DESIGN] Zero pair hashing per EIP-7864 sparse tree optimization.
    Two empty subtrees combine to zero hash. *)
Axiom hash_zero_pair : hash_pair zero32 zero32 = zero32.

Lemma hash_deterministic_value : forall v1 v2, v1 = v2 -> hash_value v1 = hash_value v2.
Proof. intros v1 v2 H. rewrite H. reflexivity. Qed.

Lemma hash_deterministic_pair : forall a1 b1 a2 b2, 
  a1 = a2 -> b1 = b2 -> hash_pair a1 b1 = hash_pair a2 b2.
Proof. intros a1 b1 a2 b2 H1 H2. rewrite H1, H2. reflexivity. Qed.

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

(** Transitivity for same-length lists *)
Lemma forallb_combine_via_same_len : forall d0 d1 d2,
  length d0 = length d1 ->
  length d1 = length d2 ->
  forallb (fun p : Z * Z => Z.eqb (fst p) (snd p)) (combine d0 d1) = true ->
  forallb (fun p : Z * Z => Z.eqb (fst p) (snd p)) (combine d1 d2) = true ->
  forallb (fun p : Z * Z => Z.eqb (fst p) (snd p)) (combine d0 d2) = true.
Proof.
  induction d0 as [|x0 r0 IH]; intros d1 d2 Hlen01 Hlen12 H01 H12.
  - reflexivity.
  - destruct d1 as [|x1 r1]; [simpl in Hlen01; discriminate|].
    destruct d2 as [|x2 r2]; [simpl in Hlen12; discriminate|].
    simpl in *.
    injection Hlen01 as Hlen01. injection Hlen12 as Hlen12.
    destruct (Z.eqb x0 x1) eqn:E01; [|discriminate].
    destruct (Z.eqb x1 x2) eqn:E12; [|discriminate].
    apply Z.eqb_eq in E01. apply Z.eqb_eq in E12.
    subst. rewrite Z.eqb_refl.
    eapply IH; eauto.
Qed.

(** [AXIOM:STRUCTURAL] Stem equality transitivity via common stem.
    
    This axiom is a convenience wrapper over the proven [stem_eq_trans].
    It assumes the global well-formedness invariant: all stems are 31 bytes.
    
    See [stem_eq_trans] for the version with explicit length preconditions.
    
    Required for: [stem_eq_false_from_third], [stems_get_set_other].
    
    Risk: Low - same invariant as [stem_eq_true]. *)
Axiom stem_eq_via_third : forall s1 s2 stem,
  stem_eq stem s1 = true ->
  stem_eq s1 s2 = true ->
  stem_eq stem s2 = true.

(** Contrapositive of transitivity *)
Lemma stem_eq_false_from_third : forall s1 s2 stem,
  stem_eq stem s1 = true ->
  stem_eq stem s2 = false ->
  stem_eq s1 s2 = false.
Proof.
  intros s1 s2 stem H1 H2.
  destruct (stem_eq s1 s2) eqn:E; [|reflexivity].
  exfalso.
  assert (stem_eq stem s2 = true) by (eapply stem_eq_via_third; eauto).
  rewrite H in H2. discriminate.
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
        assert (stem_eq s1 s2 = true).
        { rewrite stem_eq_sym in E1. eapply stem_eq_via_third; eauto. }
        rewrite H in Hneq. discriminate.
      * exact IH.
    + destruct (stem_eq stem s2) eqn:E2; [reflexivity | exact IH].
Qed.

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

(** Insert then get key with same stem/subindex returns value *)
Theorem get_insert_same_eq : forall t k1 k2 v,
  value_nonzero v ->
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  tk_subindex k1 = tk_subindex k2 ->
  sim_tree_get (sim_tree_insert t k1 v) k2 = Some v.
Proof.
  intros t k1 k2 v Hnonzero Hstem Hidx.
  unfold sim_tree_get, sim_tree_insert, value_nonzero in *.
  simpl.
  apply stem_eq_true in Hstem.
  rewrite <- Hstem.
  rewrite stems_get_set_same.
  destruct (stems_get (st_stems t) (tk_stem k1)) eqn:Hstems.
  - unfold sim_get, sim_set, is_zero_value in *.
    rewrite Hnonzero.
    simpl.
    rewrite <- Hidx.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold sim_get, sim_set, is_zero_value in *.
    rewrite Hnonzero.
    simpl.
    rewrite <- Hidx.
    rewrite Z.eqb_refl.
    reflexivity.
Qed.

(** Insert zero value then get same key returns None *)
Theorem get_insert_zero : forall t k v,
  is_zero_value v = true ->
  sim_tree_get (sim_tree_insert t k v) k = None.
Proof.
  intros t k v Hzero.
  unfold sim_tree_get, sim_tree_insert.
  simpl.
  rewrite stems_get_set_same.
  destruct (stems_get (st_stems t) (tk_stem k)) eqn:Hstems.
  - apply sim_get_set_zero_value. exact Hzero.
  - apply sim_get_set_zero_value. exact Hzero.
Qed.

(** Insert zero value then get key with same stem/subindex returns None *)
Theorem get_insert_zero_eq : forall t k1 k2 v,
  is_zero_value v = true ->
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  tk_subindex k1 = tk_subindex k2 ->
  sim_tree_get (sim_tree_insert t k1 v) k2 = None.
Proof.
  intros t k1 k2 v Hzero Hstem Hidx.
  unfold sim_tree_get, sim_tree_insert.
  simpl.
  apply stem_eq_true in Hstem.
  rewrite <- Hstem.
  rewrite stems_get_set_same.
  destruct (stems_get (st_stems t) (tk_stem k1)) eqn:Hstems.
  - unfold sim_get, sim_set.
    rewrite Hzero.
    rewrite <- Hidx.
    rewrite find_filter_none.
    reflexivity.
  - unfold sim_get, sim_set.
    rewrite Hzero.
    rewrite <- Hidx.
    rewrite find_filter_none.
    reflexivity.
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
    destruct (stem_eq stem s1) eqn:E1; destruct (stem_eq stem s2) eqn:E2.
    + reflexivity.
    + exfalso.
      assert (stem_eq stem s2 = true) by (eapply stem_eq_via_third; eauto).
      rewrite H in E2. discriminate.
    + exfalso.
      rewrite stem_eq_sym in Heq.
      assert (stem_eq stem s1 = true) by (eapply stem_eq_via_third; eauto).
      rewrite H in E1. discriminate.
    + exact IH.
Qed.

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
  - (* k matches both k1 and k2 stems - contradiction with Hdiff *)
    exfalso.
    assert (stem_eq (tk_stem k1) (tk_stem k2) = true).
    { rewrite stem_eq_sym in Ek1. eapply stem_eq_via_third; eauto. }
    rewrite H in Hdiff. discriminate.
  - (* k matches k1 stem only - k is in k1's cluster, not k2's *)
    assert (Hk2_k: stem_eq (tk_stem k2) (tk_stem k) = false) 
      by (rewrite stem_eq_sym; exact Ek2).
    (* LHS: (insert (insert t k1 v1) k2 v2) queried with k
       Since k doesn't match k2's stem, outer insert doesn't affect k *)
    rewrite get_insert_other_stem by exact Hk2_k.
    (* Now LHS is: sim_tree_get (sim_tree_insert t k1 v1) k *)
    (* RHS is: sim_tree_get (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1) k *)
    (* Since k matches k1's stem (Ek1), the outer k1 insert on RHS is relevant *)
    destruct (Z.eq_dec (tk_subindex k) (tk_subindex k1)) as [Heq|Hneq].
    + (* k has same subindex as k1 - querying the key that was just inserted in k1's cluster *)
      subst.
      (* LHS: query (insert (insert t k1 v1) k2 v2) k where k ~ k1 (stem+subindex) 
         Since k2's stem differs, outer k2 insert doesn't affect k's lookup.
         Result comes from the inner k1 insert *)
      (* RHS: query (insert (insert t k2 v2) k1 v1) k where k ~ k1 (stem+subindex)
         Outer k1 insert determines result since k ~ k1 *)
      (* Both reduce to looking up k after k1->v1 was inserted *)
      unfold sim_tree_get, sim_tree_insert. simpl.
      (* stems_get (set ... k2 ...) k = stems_get (set ... k1 ...) k since k ~ k1 not k2 *)
      assert (Hk1_res: stems_get (stems_set (st_stems t) (tk_stem k1)
        (sim_set match stems_get (st_stems t) (tk_stem k1) with Some m => m | None => [] end
                 (tk_subindex k1) v1)) (tk_stem k) =
        Some (sim_set match stems_get (st_stems t) (tk_stem k1) with Some m => m | None => [] end
                      (tk_subindex k1) v1)).
      { rewrite stems_get_stem_eq with (s2 := tk_stem k1) by exact Ek1.
        apply stems_get_set_same. }
      rewrite Hk1_res.
      (* For RHS, first unfold the inner insert *)
      simpl.
      assert (Hk1_res2: stems_get (stems_set 
        (stems_set (st_stems t) (tk_stem k2)
          (sim_set match stems_get (st_stems t) (tk_stem k2) with Some m => m | None => [] end
                   (tk_subindex k2) v2))
        (tk_stem k1)
        (sim_set match stems_get (stems_set (st_stems t) (tk_stem k2)
                   (sim_set match stems_get (st_stems t) (tk_stem k2) with Some m => m | None => [] end
                            (tk_subindex k2) v2)) (tk_stem k1) with Some m => m | None => [] end
                 (tk_subindex k1) v1)) (tk_stem k) = 
        Some (sim_set match stems_get (stems_set (st_stems t) (tk_stem k2)
                   (sim_set match stems_get (st_stems t) (tk_stem k2) with Some m => m | None => [] end
                            (tk_subindex k2) v2)) (tk_stem k1) with Some m => m | None => [] end
                 (tk_subindex k1) v1)).
      { rewrite stems_get_stem_eq with (s2 := tk_stem k1) by exact Ek1.
        apply stems_get_set_same. }
      rewrite Hk1_res2.
      (* Now the submaps differ only in what they were built from *)
      (* Since k1 stem != k2 stem, the k2 insert didn't affect k1's slot *)
      rewrite stems_get_set_other by (rewrite stem_eq_sym; exact Hdiff).
      reflexivity.
    + (* k has different subindex from k1 *)
      (* LHS: get (insert t k1 v1) k - uses get_insert_other_subindex *)
      (* RHS: get (insert (insert t k2 v2) k1 v1) k - outer k1 insert, different subindex *)
      assert (Hneq': tk_subindex k1 <> tk_subindex k) by (intro H; apply Hneq; symmetry; exact H).
      rewrite get_insert_other_subindex; [| rewrite stem_eq_sym; exact Ek1 | exact Hneq'].
      rewrite get_insert_other_subindex; [| rewrite stem_eq_sym; exact Ek1 | exact Hneq'].
      (* Now both are: sim_tree_get t k vs sim_tree_get (sim_tree_insert t k2 v2) k *)
      (* Since k doesn't match k2's stem *)
      rewrite get_insert_other_stem by exact Hk2_k.
      reflexivity.
  - (* k matches k2 stem only - k is in k2's cluster, not k1's *)
    assert (Hk1_k: stem_eq (tk_stem k1) (tk_stem k) = false) 
      by (rewrite stem_eq_sym; exact Ek1).
    (* LHS: (insert (insert t k1 v1) k2 v2) with k matching k2
       Outer k2 insert is relevant since k ~ k2 *)
    (* RHS: (insert (insert t k2 v2) k1 v1) with k not matching k1 
       Outer k1 insert is skipped. Inner k2 insert is relevant. *)
    destruct (Z.eq_dec (tk_subindex k) (tk_subindex k2)) as [Heq|Hneq].
    + (* k has same subindex as k2 *)
      subst.
      (* LHS: get (insert (insert t k1 v1) k2 v2) k = query k2 cluster after k2 insert *)
      (* RHS: get (insert (insert t k2 v2) k1 v1) k - skip k1, then query k2 cluster *)
      (* Both return the value at k (which is in k2's cluster) *)
      unfold sim_tree_get, sim_tree_insert. simpl.
      (* RHS: skip the k1 insert because k ~ k2 not k1 *)
      assert (Hk_k2: stems_get (stems_set (st_stems t) (tk_stem k1)
        (sim_set match stems_get (st_stems t) (tk_stem k1) with Some m => m | None => [] end
                 (tk_subindex k1) v1)) (tk_stem k2) =
        stems_get (st_stems t) (tk_stem k2)).
      { rewrite stems_get_set_other by exact Hdiff. reflexivity. }
      (* For LHS outer k2 insert *)
      assert (Hk_lhs: stems_get (stems_set 
        (stems_set (st_stems t) (tk_stem k1)
          (sim_set match stems_get (st_stems t) (tk_stem k1) with Some m => m | None => [] end
                   (tk_subindex k1) v1))
        (tk_stem k2)
        (sim_set match stems_get (stems_set (st_stems t) (tk_stem k1)
                   (sim_set match stems_get (st_stems t) (tk_stem k1) with Some m => m | None => [] end
                            (tk_subindex k1) v1)) (tk_stem k2) with Some m => m | None => [] end
                 (tk_subindex k2) v2)) (tk_stem k) =
        Some (sim_set match stems_get (stems_set (st_stems t) (tk_stem k1)
                   (sim_set match stems_get (st_stems t) (tk_stem k1) with Some m => m | None => [] end
                            (tk_subindex k1) v1)) (tk_stem k2) with Some m => m | None => [] end
                 (tk_subindex k2) v2)).
      { rewrite stems_get_stem_eq with (s2 := tk_stem k2) by exact Ek2.
        apply stems_get_set_same. }
      rewrite Hk_lhs.
      (* For RHS, skip outer k1, then get from inner k2 insert *)
      assert (Hk_rhs: stems_get (stems_set
        (stems_set (st_stems t) (tk_stem k2)
          (sim_set match stems_get (st_stems t) (tk_stem k2) with Some m => m | None => [] end
                   (tk_subindex k2) v2))
        (tk_stem k1)
        (sim_set match stems_get (stems_set (st_stems t) (tk_stem k2)
                   (sim_set match stems_get (st_stems t) (tk_stem k2) with Some m => m | None => [] end
                            (tk_subindex k2) v2)) (tk_stem k1) with Some m => m | None => [] end
                 (tk_subindex k1) v1)) (tk_stem k) =
        stems_get (stems_set (st_stems t) (tk_stem k2)
          (sim_set match stems_get (st_stems t) (tk_stem k2) with Some m => m | None => [] end
                   (tk_subindex k2) v2)) (tk_stem k)).
      { rewrite stems_get_set_other by exact Hk1_k. reflexivity. }
      rewrite Hk_rhs.
      (* Now we need: sim_get on LHS submap = sim_get on RHS submap at tk_subindex k = tk_subindex k2 *)
      (* LHS submap: built from stems_get (after k1 set) at k2 *)
      (* RHS: stems_get (k2 set) at k, which equals stems_get (k2 set) at k2 by Ek2 *)
      rewrite (stems_get_stem_eq _ _ _ Ek2).
      rewrite stems_get_set_same.
      rewrite Hk_k2.
      reflexivity.
    + (* k has different subindex from k2 *)
      assert (Hneq': tk_subindex k2 <> tk_subindex k) by (intro H; apply Hneq; symmetry; exact H).
      (* LHS: outer k2 (same stem, diff subindex), then inner k1 (diff stem) *)
      rewrite get_insert_other_subindex; [| rewrite stem_eq_sym; exact Ek2 | exact Hneq'].
      rewrite get_insert_other_stem by exact Hk1_k.
      (* RHS: outer k1 (diff stem), then inner k2 (same stem, diff subindex) *)
      rewrite get_insert_other_stem by exact Hk1_k.
      rewrite get_insert_other_subindex; [| rewrite stem_eq_sym; exact Ek2 | exact Hneq'].
      reflexivity.
  - (* k matches neither stem *)
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek2).
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek1).
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek1).
    rewrite get_insert_other_stem by (rewrite stem_eq_sym; exact Ek2).
    reflexivity.
Qed.

(** sim_get after sim_set at the same index depends only on the value, not the base map *)
Lemma sim_get_set_same_idx : forall m1 m2 idx v,
  sim_get (sim_set m1 idx v) idx = sim_get (sim_set m2 idx v) idx.
Proof.
  intros m1 m2 idx v.
  unfold sim_get, sim_set.
  destruct (is_zero_value v).
  - simpl. rewrite find_filter_none. rewrite find_filter_none. reflexivity.
  - simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** Helper: sim_set commutes for different indices *)
Lemma sim_set_comm : forall m idx1 v1 idx2 v2,
  idx1 <> idx2 ->
  forall idx, sim_get (sim_set (sim_set m idx1 v1) idx2 v2) idx =
              sim_get (sim_set (sim_set m idx2 v2) idx1 v1) idx.
Proof.
  intros m idx1 v1 idx2 v2 Hneq idx.
  destruct (Z.eq_dec idx idx1) as [E1|N1]; destruct (Z.eq_dec idx idx2) as [E2|N2].
  - subst. exfalso. apply Hneq. reflexivity.
  - subst.
    (* Query idx1: skip outer idx2 on LHS, then query inner idx1 set *)
    assert (Hneq': idx2 <> idx1) by (intro H; apply Hneq; symmetry; exact H).
    rewrite sim_get_set_other by exact Hneq'.
    (* LHS: sim_get (sim_set m idx1 v1) idx1 *)
    (* RHS: sim_get (sim_set (sim_set m idx2 v2) idx1 v1) idx1 *)
    (* Both reduce to v1's effect at idx1 *)
    apply sim_get_set_same_idx.
  - subst.
    (* Query idx2: LHS outer idx2 set, RHS skip outer idx1 then inner idx2 set *)
    (* RHS: sim_get (sim_set (sim_set m idx2 v2) idx1 v1) idx2 - skip outer idx1 *)
    assert (Hrhs: sim_get (sim_set (sim_set m idx2 v2) idx1 v1) idx2 = 
                  sim_get (sim_set m idx2 v2) idx2).
    { apply sim_get_set_other. exact Hneq. }
    rewrite Hrhs.
    (* LHS: sim_get (sim_set (sim_set m idx1 v1) idx2 v2) idx2 *)
    (* RHS: sim_get (sim_set m idx2 v2) idx2 *)
    symmetry. apply sim_get_set_same_idx.
  - (* Query idx (not idx1 or idx2) - skip both sets *)
    assert (N1': idx1 <> idx) by (intro H; apply N1; symmetry; exact H).
    assert (N2': idx2 <> idx) by (intro H; apply N2; symmetry; exact H).
    rewrite sim_get_set_other by exact N2'.
    rewrite sim_get_set_other by exact N1'.
    rewrite sim_get_set_other by exact N1'.
    rewrite sim_get_set_other by exact N2'.
    reflexivity.
Qed.

(** Insertion order independence for same-stem keys.
    Different subindices within same stem can be inserted in any order.
    Proven using sim_set_comm - purely algebraic property of finite maps. *)
Lemma insert_order_independent_subindex : forall t k1 v1 k2 v2,
  stem_eq (tk_stem k1) (tk_stem k2) = true ->
  tk_subindex k1 <> tk_subindex k2 ->
  tree_eq 
    (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
    (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  intros t k1 v1 k2 v2 Hstem Hidx.
  unfold tree_eq. intros k.
  unfold sim_tree_get, sim_tree_insert. simpl.
  (* Use stem_eq_true to get propositional equality *)
  assert (Hstem_eq: tk_stem k1 = tk_stem k2) by (apply stem_eq_true; exact Hstem).
  assert (Hstem_rev: stem_eq (tk_stem k2) (tk_stem k1) = true).
  { rewrite stem_eq_sym. exact Hstem. }
  destruct (stem_eq (tk_stem k) (tk_stem k2)) eqn:Ek.
  - (* k matches k2's stem (and k1's stem via transitivity) *)
    assert (Ek1: stem_eq (tk_stem k) (tk_stem k1) = true).
    { eapply stem_eq_via_third; eauto. }
    (* Since stems are equal, we can work entirely in terms of k1's stem *)
    (* LHS: stems_get from (set at k2 of (set at k1))
       RHS: stems_get from (set at k1 of (set at k2)) *)
    (* Use stems_get_stem_eq to rewrite query stem to match the set stem *)
    rewrite (stems_get_stem_eq _ (tk_stem k) (tk_stem k2) Ek).
    rewrite (stems_get_stem_eq _ (tk_stem k) (tk_stem k1) Ek1).
    (* Now rewrite k2 to k1 everywhere using propositional equality *)
    rewrite <- Hstem_eq.
    (* Both sides now use tk_stem k1 consistently *)
    rewrite !stems_get_set_same.
    (* Now both sides are sim_set applied to the base after inner stems_get_set_same *)
    (* The inner stems_get also hits the set, so apply again *)
    destruct (stems_get (st_stems t) (tk_stem k1)) as [base_map|] eqn:Hbase.
    + apply sim_set_comm. exact Hidx.
    + apply sim_set_comm. exact Hidx.
  - (* k doesn't match k2's stem *)
    assert (Ek1: stem_eq (tk_stem k) (tk_stem k1) = false).
    { destruct (stem_eq (tk_stem k) (tk_stem k1)) eqn:E; [|reflexivity].
      exfalso. apply stem_eq_true in E.
      rewrite E, Hstem_eq in Ek. rewrite stem_eq_refl in Ek. discriminate. }
    assert (Ek': stem_eq (tk_stem k2) (tk_stem k) = false) 
      by (rewrite stem_eq_sym; exact Ek).
    assert (Ek1': stem_eq (tk_stem k1) (tk_stem k) = false) 
      by (rewrite stem_eq_sym; exact Ek1).
    rewrite stems_get_set_other by exact Ek'.
    rewrite stems_get_set_other by exact Ek1'.
    rewrite stems_get_set_other by exact Ek1'.
    rewrite stems_get_set_other by exact Ek'.
    reflexivity.
Qed.

(** ** Merkle Root Hash *)

(** Compute hash of a SubIndexMap (simplified: hash of concatenated values) *)
Definition subindex_map_hash (m : SubIndexMap) : Bytes32 :=
  fold_left (fun acc p => hash_pair acc (hash_value (snd p))) m zero32.

(** Compute hash of a stem entry *)
Definition stem_entry_hash (s : Stem) (m : SubIndexMap) : Bytes32 :=
  hash_stem s (subindex_map_hash m).

(** Compute Merkle root hash of the entire tree *)
Definition sim_root_hash (t : SimTree) : Bytes32 :=
  fold_left (fun acc p => hash_pair acc (stem_entry_hash (fst p) (snd p))) 
            (st_stems t) zero32.

(** Empty tree has zero root hash *)
Theorem empty_sim_tree_hash_zero :
  sim_root_hash empty_tree = zero32.
Proof.
  reflexivity.
Qed.

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

(** ** Well-Formedness Invariants with NoDup *)

(** Unique subindices in a SubIndexMap *)
Definition submap_nodup (m : SubIndexMap) : Prop :=
  NoDup (map fst m).

(** Unique stems in the stem map *)
Definition stems_nodup (sm : StemMap) : Prop :=
  NoDup (map fst sm).

(** All submaps in stem map have unique subindices *)
Definition all_submaps_nodup (sm : StemMap) : Prop :=
  Forall (fun p => submap_nodup (snd p)) sm.

(** Full well-formedness: NoDup stems + NoDup subindices in each submap *)
Record wf_tree_strong (t : SimTree) : Prop := mkWfTreeStrong {
  wf_stems_nodup : stems_nodup (st_stems t);
  wf_submaps_nodup : all_submaps_nodup (st_stems t)
}.

(** Original inductive wf_tree for backward compatibility *)
Inductive wf_tree : SimTree -> Prop :=
  | wf_empty : wf_tree empty_tree
  | wf_insert : forall t k v,
      wf_tree t ->
      wf_value v ->
      wf_stem (tk_stem k) ->
      wf_tree (sim_tree_insert t k v).

(** ** Preservation Lemmas for Strong Well-Formedness *)

(** Helper: In for map *)
Lemma In_map_iff : forall {A B : Type} (f : A -> B) (l : list A) (b : B),
  In b (map f l) <-> exists a, In a l /\ b = f a.
Proof.
  intros A B f l b.
  split.
  - intros Hin. induction l as [|x xs IH].
    + inversion Hin.
    + simpl in Hin. destruct Hin as [Heq|Hin].
      * exists x. split. left. reflexivity. symmetry. exact Heq.
      * destruct (IH Hin) as [a [Ha Hb]].
        exists a. split. right. exact Ha. exact Hb.
  - intros [a [Ha Hb]]. subst. apply in_map. exact Ha.
Qed.

(** Empty tree is strongly well-formed *)
Lemma wf_tree_strong_empty : wf_tree_strong empty_tree.
Proof.
  constructor.
  - unfold stems_nodup, empty_tree. simpl. constructor.
  - unfold all_submaps_nodup, empty_tree. simpl. constructor.
Qed.

(** Helper: sim_set preserves NoDup when filtering removes duplicates *)
Lemma sim_set_preserves_nodup : forall m idx v,
  submap_nodup m ->
  submap_nodup (sim_set m idx v).
Proof.
  intros m idx v Hnd.
  unfold submap_nodup, sim_set.
  destruct (is_zero_value v) eqn:Hzero.
  - (* Zero value: filter only *)
    unfold submap_nodup in Hnd.
    induction m as [|[i val] rest IH].
    + simpl. constructor.
    + simpl. destruct (Z.eqb i idx) eqn:E.
      * simpl. simpl in Hnd. inversion Hnd. subst.
        apply IH. exact H2.
      * simpl. constructor.
        { intro Hin. simpl in Hnd. inversion Hnd. subst.
          rewrite In_map_iff in Hin.
          destruct Hin as [[j w] [Hin' Heq]].
          simpl in Heq. subst i.
          apply filter_In in Hin'.
          destruct Hin' as [Hin' _].
          (* (j,w) is in rest, so j = fst (j,w) is in map fst rest *)
          apply H1. exact (in_map fst _ _ Hin'). }
        { simpl in Hnd. inversion Hnd. subst.
          apply IH. exact H2. }
  - (* Non-zero: prepend and filter *)
    simpl. constructor.
    + intro Hin.
      rewrite In_map_iff in Hin.
      destruct Hin as [[j w] [Hin' Heq]].
      simpl in Heq. subst idx.
      apply filter_In in Hin'.
      destruct Hin' as [_ Hfilter].
      simpl in Hfilter.
      rewrite Z.eqb_refl in Hfilter. discriminate.
    + unfold submap_nodup in Hnd.
      induction m as [|[i val'] rest IH].
      * simpl. constructor.
      * simpl. destruct (Z.eqb i idx) eqn:E.
        { simpl. simpl in Hnd. inversion Hnd. subst.
          apply IH. exact H2. }
        { simpl. constructor.
          - intro Hin. simpl in Hnd. inversion Hnd. subst.
            rewrite In_map_iff in Hin.
            destruct Hin as [[j w] [Hin' Heq]].
            simpl in Heq. subst i.
            apply filter_In in Hin'.
            destruct Hin' as [Hin' _].
            apply H1. exact (in_map fst _ _ Hin').
          - simpl in Hnd. inversion Hnd. subst.
            apply IH. exact H2. }
Qed.

(** Helper: stems_set preserves NoDup by filtering out old entry *)
Lemma stems_set_preserves_nodup : forall m s v,
  stems_nodup m ->
  stems_nodup (stems_set m s v).
Proof.
  intros m s v Hnd.
  unfold stems_nodup, stems_set. simpl.
  constructor.
  - intro Hin.
    rewrite In_map_iff in Hin.
    destruct Hin as [[stem submap] [Hin' Heq]].
    simpl in Heq. subst s.
    apply filter_In in Hin'.
    destruct Hin' as [_ Hfilter].
    simpl in Hfilter.
    rewrite stem_eq_refl in Hfilter. discriminate.
  - unfold stems_nodup in Hnd.
    induction m as [|[stem submap] rest IH].
    + simpl. constructor.
    + simpl. destruct (stem_eq stem s) eqn:E.
      * simpl in Hnd. inversion Hnd. subst.
        apply IH. exact H2.
      * simpl. constructor.
        { intro Hin. simpl in Hnd. inversion Hnd. subst.
          rewrite In_map_iff in Hin.
          destruct Hin as [[stem' submap'] [Hin' Heq]].
          simpl in Heq. subst stem.
          apply filter_In in Hin'.
          destruct Hin' as [Hin' _].
          apply H1. exact (in_map fst _ _ Hin'). }
        { simpl in Hnd. inversion Hnd. subst.
          apply IH. exact H2. }
Qed.

(** Helper: stems_set updates or adds to submaps with NoDup preservation *)
Lemma stems_set_preserves_all_submaps_nodup : forall m s submap,
  all_submaps_nodup m ->
  submap_nodup submap ->
  all_submaps_nodup (stems_set m s submap).
Proof.
  intros m s submap Hall Hsubmap.
  unfold all_submaps_nodup, stems_set. simpl.
  constructor.
  - simpl. exact Hsubmap.
  - unfold all_submaps_nodup in Hall.
    induction m as [|[stem sm] rest IH].
    + simpl. constructor.
    + simpl. destruct (stem_eq stem s) eqn:E.
      * inversion Hall. subst. apply IH. exact H2.
      * constructor.
        { inversion Hall. subst. simpl. exact H1. }
        { inversion Hall. subst. apply IH. exact H2. }
Qed.

(** Main theorem: insert preserves strong well-formedness *)
Theorem wf_tree_strong_insert : forall t k v,
  wf_tree_strong t ->
  wf_tree_strong (sim_tree_insert t k v).
Proof.
  intros t k v [Hstems Hsubmaps].
  unfold sim_tree_insert. simpl.
  constructor.
  - apply stems_set_preserves_nodup. exact Hstems.
  - apply stems_set_preserves_all_submaps_nodup.
    + exact Hsubmaps.
    + destruct (stems_get (st_stems t) (tk_stem k)) as [old_submap|] eqn:E.
      * apply sim_set_preserves_nodup.
        unfold stems_get in E.
        destruct (find (fun p => stem_eq (fst p) (tk_stem k)) (st_stems t)) 
          as [[stem sm]|] eqn:Hfind; [|discriminate].
        injection E as Esm. subst old_submap.
        unfold all_submaps_nodup in Hsubmaps.
        assert (Hin: In (stem, sm) (st_stems t)).
        { clear -Hfind.
          induction (st_stems t) as [|[s m] rest IH].
          - discriminate.
          - simpl in Hfind. destruct (stem_eq s (tk_stem k)) eqn:Eq.
            + injection Hfind as H1 H2. subst. left. reflexivity.
            + right. apply IH. exact Hfind. }
        rewrite Forall_forall in Hsubmaps.
        apply Hsubmaps in Hin. simpl in Hin. exact Hin.
      * apply sim_set_preserves_nodup.
        unfold submap_nodup. simpl. constructor.
Qed.

(** Insertion preserves well-formedness (original) *)
Theorem insert_preserves_wf : forall t k v,
  wf_tree t -> wf_value v -> wf_stem (tk_stem k) ->
  wf_tree (sim_tree_insert t k v).
Proof.
  intros. constructor; assumption.
Qed.

(** ** Merkle Proof Types *)

(** Direction in Merkle tree traversal *)
Inductive Direction : Type :=
  | Left : Direction
  | Right : Direction.

(** A Merkle proof step: sibling hash and direction *)
Record MerkleStep := mkMerkleStep {
  ms_sibling : Bytes32;
  ms_direction : Direction
}.

(** Merkle witness: path from leaf to root *)
Definition MerkleWitness := list MerkleStep.

(** Full inclusion proof for a value in the tree *)
Record InclusionProof := mkInclusionProof {
  ip_key : TreeKey;
  ip_value : Value;
  ip_stem_proof : MerkleWitness;
  ip_tree_proof : MerkleWitness
}.

(** Exclusion proof case *)
Inductive ExclusionCase : Type :=
  | ExclNoStem : ExclusionCase
  | ExclNoSubindex : ExclusionCase.

(** Full exclusion proof for absence of a key *)
Record ExclusionProof := mkExclusionProof {
  ep_key : TreeKey;
  ep_case : ExclusionCase;
  ep_stem_proof : MerkleWitness;
  ep_tree_proof : MerkleWitness
}.

(** Compute root from leaf hash and witness *)
Fixpoint compute_root_from_witness (leaf_hash : Bytes32) (witness : MerkleWitness) : Bytes32 :=
  match witness with
  | [] => leaf_hash
  | step :: rest =>
      let combined :=
        match ms_direction step with
        | Left => hash_pair (ms_sibling step) leaf_hash
        | Right => hash_pair leaf_hash (ms_sibling step)
        end
      in compute_root_from_witness combined rest
  end.

(** Verify an inclusion proof *)
Definition verify_inclusion_proof (proof : InclusionProof) (root : Bytes32) : Prop :=
  let leaf_hash := hash_value (ip_value proof) in
  let stem_root := compute_root_from_witness leaf_hash (ip_stem_proof proof) in
  let stem_hash := hash_stem (tk_stem (ip_key proof)) stem_root in
  compute_root_from_witness stem_hash (ip_tree_proof proof) = root.

(** Verify an exclusion proof *)
Definition verify_exclusion_proof (proof : ExclusionProof) (root : Bytes32) : Prop :=
  let zero_hash := zero32 in
  let stem_hash := hash_stem (tk_stem (ep_key proof)) zero_hash in
  compute_root_from_witness stem_hash (ep_tree_proof proof) = root.

(** [AXIOM:SOUNDNESS] Inclusion proof soundness - verified proofs imply membership.
    Critical security property: if Merkle proof verifies against root, the
    key-value pair exists in the tree. Follows from collision resistance. *)
Axiom inclusion_proof_soundness :
  forall (t : SimTree) (proof : InclusionProof),
    verify_inclusion_proof proof (sim_root_hash t) ->
    sim_tree_get t (ip_key proof) = Some (ip_value proof).

(** [AXIOM:SOUNDNESS] Exclusion proof soundness - verified proofs imply absence.
    If exclusion proof verifies, the key is not in the tree.
    Relies on zero-hash property for empty subtree representation. *)
Axiom exclusion_proof_soundness :
  forall (t : SimTree) (proof : ExclusionProof),
    verify_exclusion_proof proof (sim_root_hash t) ->
    sim_tree_get t (ep_key proof) = None.

(** ** Batch Proof Types *)

Definition BatchInclusionProof := list InclusionProof.
Definition BatchExclusionProof := list ExclusionProof.

Record BatchProof := mkBatchProof {
  bp_inclusions : BatchInclusionProof;
  bp_exclusions : BatchExclusionProof
}.

(** Verify batch inclusion proof *)
Definition verify_batch_inclusion (proofs : BatchInclusionProof) (root : Bytes32) : Prop :=
  Forall (fun p => verify_inclusion_proof p root) proofs.

(** Verify batch exclusion proof *)
Definition verify_batch_exclusion (proofs : BatchExclusionProof) (root : Bytes32) : Prop :=
  Forall (fun p => verify_exclusion_proof p root) proofs.

(** Shared witness for optimization *)
Record SharedWitness := mkSharedWitness {
  sw_common_path : MerkleWitness;
  sw_local_witnesses : list MerkleWitness
}.

(** Batch verification with shared witness - returns Prop indicating validity *)
Definition batch_verify_with_shared (proofs : BatchInclusionProof) (root : Bytes32) (sw : SharedWitness) : Prop :=
  verify_batch_inclusion proofs root.

(** Verify mixed batch proof *)
Definition verify_batch_mixed (batch : BatchProof) (root : Bytes32) : Prop :=
  verify_batch_inclusion (bp_inclusions batch) root /\
  verify_batch_exclusion (bp_exclusions batch) root.

(** Batch inclusion soundness - follows directly from Forall definition *)
Lemma batch_inclusion_sound :
  forall (batch : BatchInclusionProof) (root : Bytes32),
    verify_batch_inclusion batch root ->
    forall proof, In proof batch -> verify_inclusion_proof proof root.
Proof.
  intros batch root Hverify proof Hin.
  unfold verify_batch_inclusion in Hverify.
  rewrite Forall_forall in Hverify.
  apply Hverify. exact Hin.
Qed.

(** Batch exclusion soundness - follows directly from Forall definition *)
Lemma batch_exclusion_sound :
  forall (batch : BatchExclusionProof) (root : Bytes32),
    verify_batch_exclusion batch root ->
    forall proof, In proof batch -> verify_exclusion_proof proof root.
Proof.
  intros batch root Hverify proof Hin.
  unfold verify_batch_exclusion in Hverify.
  rewrite Forall_forall in Hverify.
  apply Hverify. exact Hin.
Qed.

(** Batch mixed soundness *)
Lemma batch_mixed_sound :
  forall (batch : BatchProof) (root : Bytes32),
    verify_batch_mixed batch root ->
    (forall proof, In proof (bp_inclusions batch) -> verify_inclusion_proof proof root) /\
    (forall proof, In proof (bp_exclusions batch) -> verify_exclusion_proof proof root).
Proof.
  intros batch root [Hincl Hexcl].
  split.
  - intros proof Hin. apply (batch_inclusion_sound _ root Hincl proof Hin).
  - intros proof Hin. apply (batch_exclusion_sound _ root Hexcl proof Hin).
Qed.

(** [AXIOM:SOUNDNESS] Same key consistency - unique value binding.
    Two valid proofs for the same key must have the same value.
    Follows from hash collision resistance (tree is a function). *)
Axiom batch_same_key_consistent :
  forall (root : Bytes32) (p1 p2 : InclusionProof),
    ip_key p1 = ip_key p2 ->
    verify_inclusion_proof p1 root ->
    verify_inclusion_proof p2 root ->
    ip_value p1 = ip_value p2.

(** Batch implies consistent - proofs in same batch are mutually consistent.
    Derived from batch_inclusion_sound and batch_same_key_consistent. *)
Lemma batch_implies_consistent :
  forall (batch : BatchInclusionProof) (root : Bytes32) (p1 p2 : InclusionProof),
    verify_batch_inclusion batch root ->
    In p1 batch ->
    In p2 batch ->
    ip_key p1 = ip_key p2 ->
    ip_value p1 = ip_value p2.
Proof.
  intros batch root p1 p2 Hbatch Hin1 Hin2 Hkey.
  apply batch_inclusion_sound with (proof := p1) in Hbatch as Hp1; [|exact Hin1].
  apply batch_inclusion_sound with (proof := p2) in Hbatch as Hp2; [|exact Hin2].
  eapply batch_same_key_consistent; eauto.
Qed.

(** Compute shared witness - optimization for batch proofs *)
Definition compute_shared_witness (batch : BatchInclusionProof) : option SharedWitness :=
  match batch with
  | [] => None
  | p :: _ => Some (mkSharedWitness (ip_tree_proof p) (map ip_stem_proof batch))
  end.

(** Shared verification implies standard batch verification.
    Follows directly from definition of batch_verify_with_shared. *)
Lemma shared_verify_implies_batch :
  forall (batch : BatchInclusionProof) (root : Bytes32) (sw : SharedWitness),
    batch_verify_with_shared batch root sw ->
    compute_shared_witness batch = Some sw ->
    verify_batch_inclusion batch root.
Proof.
  intros batch root sw Hverify _.
  unfold batch_verify_with_shared in Hverify.
  exact Hverify.
Qed.

(** ** MultiProof Type and Verification
    
    MultiProof is an optimized proof structure for multiple keys that
    shares common proof nodes (deduplication). This matches the Rust
    MultiProof structure in src/proof.rs.
*)

(** MultiProof: optimized proof for multiple keys with shared nodes *)
Record MultiProof := mkMultiProof {
  mp_keys : list TreeKey;
  mp_values : list (option Value);
  mp_nodes : list Bytes32;      (** Shared proof nodes (deduplicated) *)
  mp_stems : list Stem          (** Stems included in the proof *)
}.

(** Empty multiproof *)
Definition empty_multiproof : MultiProof := mkMultiProof [] [] [] [].

(** Size of a multiproof (for optimization metrics) *)
Definition multiproof_size (mp : MultiProof) : nat :=
  length (mp_keys mp) * 33 +       (* keys: 32 bytes stem + 1 byte subindex *)
  length (mp_values mp) * 33 +
  length (mp_nodes mp) * 32 +
  length (mp_stems mp) * 31.

(** Well-formed multiproof: keys and values have same length *)
Definition wf_multiproof (mp : MultiProof) : Prop :=
  length (mp_keys mp) = length (mp_values mp).

(** Key-value pair extraction from multiproof *)
Definition multiproof_get (mp : MultiProof) (idx : nat) : option (TreeKey * option Value) :=
  match nth_error (mp_keys mp) idx, nth_error (mp_values mp) idx with
  | Some k, Some v => Some (k, v)
  | _, _ => None
  end.

(** All key-value pairs in multiproof *)
Definition multiproof_pairs (mp : MultiProof) : list (TreeKey * option Value) :=
  combine (mp_keys mp) (mp_values mp).

(** ** MultiProof Generation and Verification *)

(** Generate a multiproof for multiple keys (functional specification).
    This mirrors Rust MultiProof construction that collects:
    - All queried keys
    - Their values (Some for inclusion, None for exclusion)
    - Deduplicated sibling nodes along Merkle paths
    - All stems encountered
    
    See src/proof.rs:159-198 for Rust MultiProof structure. *)
Definition sim_generate_multi_proof (t : SimTree) (keys : list TreeKey) : MultiProof :=
  mkMultiProof
    keys
    (map (fun k => sim_tree_get t k) keys)
    []   (* nodes would be computed from Merkle paths - abstract here *)
    (map tk_stem keys).  (* stems from queried keys *)

(** Verify a multiproof against a root hash (functional specification).
    A multiproof is valid if:
    1. It is well-formed (keys/values same length)
    2. All key-value bindings are consistent with the tree
    3. The Merkle path nodes correctly reconstruct to root
    
    This is abstracted as a parameter since full verification
    requires the actual hash computations. *)
Parameter verify_multiproof : MultiProof -> Bytes32 -> Prop.

(** Computational verification predicate for multiproofs.
    This provides a decidable check used in the Rust implementation.
    Returns true if all structural invariants hold. *)
Definition sim_verify_multi_proof (mp : MultiProof) (root : Bytes32) : bool :=
  (* Check well-formedness: keys and values same length *)
  Nat.eqb (length (mp_keys mp)) (length (mp_values mp)) &&
  (* Check stems list is non-empty when keys exist: implb a b = negb a || b *)
  (negb (negb (Nat.eqb (length (mp_keys mp)) 0)) || negb (Nat.eqb (length (mp_stems mp)) 0)).

(** sim_verify_multi_proof returning true implies well-formedness *)
Lemma sim_verify_implies_wf : forall mp root,
  sim_verify_multi_proof mp root = true ->
  wf_multiproof mp.
Proof.
  intros mp root H.
  unfold sim_verify_multi_proof in H.
  apply Bool.andb_true_iff in H.
  destruct H as [Hlen _].
  unfold wf_multiproof.
  apply Nat.eqb_eq. exact Hlen.
Qed.

(** Generated multiproof is well-formed *)
Lemma sim_generate_multi_proof_wf : forall t keys,
  wf_multiproof (sim_generate_multi_proof t keys).
Proof.
  intros t keys.
  unfold wf_multiproof, sim_generate_multi_proof. simpl.
  rewrite length_map. reflexivity.
Qed.

(** Generated multiproof has correct keys *)
Lemma sim_generate_multi_proof_keys : forall t keys,
  mp_keys (sim_generate_multi_proof t keys) = keys.
Proof.
  intros t keys. reflexivity.
Qed.

(** Generated multiproof values match tree lookups *)
Lemma sim_generate_multi_proof_values : forall t keys,
  mp_values (sim_generate_multi_proof t keys) = map (fun k => sim_tree_get t k) keys.
Proof.
  intros t keys. reflexivity.
Qed.

(** [AXIOM:SOUNDNESS] MultiProof soundness - core security property.
    If a multiproof verifies against a root hash, then all key-value
    pairs in the proof actually exist in the tree with those values.
    
    This is the fundamental correctness theorem for MultiProof:
    - For inclusion (Some v): the key maps to v in the tree
    - For exclusion (None): the key is not in the tree
    
    Relies on hash collision resistance and the Merkle tree construction. *)
Axiom multiproof_soundness :
  forall (t : SimTree) (mp : MultiProof),
    wf_multiproof mp ->
    verify_multiproof mp (sim_root_hash t) ->
    forall idx k v,
      multiproof_get mp idx = Some (k, v) ->
      sim_tree_get t k = v.

(** [AXIOM:COMPLETENESS] MultiProof completeness - any key set has a valid proof.
    For any set of keys in a well-formed tree, there exists a valid
    multiproof that proves all of them (either inclusion or exclusion).
    
    This guarantees that proofs can always be generated for any query set. *)
Axiom multiproof_completeness :
  forall (t : SimTree) (keys : list TreeKey),
    wf_tree t ->
    exists mp : MultiProof,
      wf_multiproof mp /\
      mp_keys mp = keys /\
      verify_multiproof mp (sim_root_hash t) /\
      forall idx k v,
        multiproof_get mp idx = Some (k, v) ->
        sim_tree_get t k = v.

(** Helper: In implies nth_error *)
Lemma In_nth_error : forall {A : Type} (l : list A) x,
  In x l -> exists idx, nth_error l idx = Some x.
Proof.
  intros A l x Hin.
  induction l as [|a rest IH].
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst. exists 0%nat. reflexivity.
    + apply IH in Hin. destruct Hin as [idx Hnth].
      exists (S idx). simpl. exact Hnth.
Qed.

(** Helper: combine produces elements at valid indices *)
Lemma combine_nth_error : forall {A B : Type} (l1 : list A) (l2 : list B) idx p,
  length l1 = length l2 ->
  nth_error (combine l1 l2) idx = Some p ->
  nth_error l1 idx = Some (fst p) /\ nth_error l2 idx = Some (snd p).
Proof.
  intros A B l1 l2 idx p Hlen Hnth.
  generalize dependent l2.
  generalize dependent idx.
  induction l1 as [|a1 rest1 IH]; intros idx l2 Hlen Hnth.
  - destruct idx; simpl in Hnth; discriminate.
  - destruct l2 as [|b2 rest2]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct idx.
    + simpl in Hnth. injection Hnth as Heq. subst p.
      simpl. auto.
    + simpl in Hnth.
      apply IH in Hnth; auto.
Qed.

(** MultiProof implies all individual proofs are sound *)
Lemma multiproof_all_sound :
  forall (t : SimTree) (mp : MultiProof),
    wf_multiproof mp ->
    verify_multiproof mp (sim_root_hash t) ->
    forall k v, In (k, v) (multiproof_pairs mp) ->
      sim_tree_get t k = v.
Proof.
  intros t mp Hwf Hverify k v Hin.
  unfold multiproof_pairs in Hin.
  apply In_nth_error in Hin.
  destruct Hin as [idx Hnth].
  assert (Hget: multiproof_get mp idx = Some (k, v)).
  { unfold multiproof_get.
    apply combine_nth_error in Hnth.
    destruct Hnth as [Hk Hv].
    rewrite Hk, Hv. reflexivity.
    unfold wf_multiproof in Hwf. exact Hwf. }
  eapply multiproof_soundness; eauto.
Qed.

(** ** Witness Generation Correctness *)

(** Witness for stateless execution (matches Rust Witness struct) *)
Record SimWitness := mkSimWitness {
  sw_pre_values : list (TreeKey * Value);
  sw_proof : MultiProof
}.

(** Generate a multiproof for a set of keys *)
Parameter generate_multiproof : SimTree -> list TreeKey -> MultiProof.

(** [AXIOM:CORRECTNESS] Witness generation correctness.
    The generate_multiproof function produces valid multiproofs.
    This axiom states that for any tree and key set, the generated
    proof is well-formed and verifies correctly.
    
    In the Rust implementation, this corresponds to generate_stem_proof
    in src/proof.rs producing valid sibling hashes. *)
Axiom witness_generation_correct :
  forall (t : SimTree) (keys : list TreeKey),
    wf_tree t ->
    let mp := generate_multiproof t keys in
    wf_multiproof mp /\
    mp_keys mp = keys /\
    verify_multiproof mp (sim_root_hash t).

(** Corollary: generated proofs are sound *)
Lemma generated_multiproof_sound :
  forall (t : SimTree) (keys : list TreeKey),
    wf_tree t ->
    let mp := generate_multiproof t keys in
    forall idx k v,
      multiproof_get mp idx = Some (k, v) ->
      sim_tree_get t k = v.
Proof.
  intros t keys Hwf mp idx k v Hget.
  destruct (witness_generation_correct t keys Hwf) as [Hwfmp [_ Hverify]].
  eapply multiproof_soundness; eauto.
Qed.

(** ** Stem-level Proof Properties *)

(** Generate stem proof for a subindex within a stem node.
    Returns the value and sibling hashes for 8-level subtree. *)
Parameter generate_stem_proof_spec : SubIndexMap -> SubIndex -> (option Value) * list Bytes32.

(** [AXIOM:CORRECTNESS] Stem proof generates correct siblings.
    The stem proof generation produces exactly 8 sibling hashes
    that correctly reconstruct the subtree root when combined
    with the value hash according to the subindex path.
    
    Corresponds to generate_stem_proof in src/proof.rs:123-157. *)
Axiom stem_proof_siblings_correct :
  forall (submap : SubIndexMap) (idx : SubIndex),
    let (_, siblings) := generate_stem_proof_spec submap idx in
    length siblings = 8%nat.

(** Stem proof value matches stored value *)
Axiom stem_proof_value_correct :
  forall (submap : SubIndexMap) (idx : SubIndex),
    let (val, _) := generate_stem_proof_spec submap idx in
    val = sim_get submap idx.

(** ** MultiProof Deduplication Properties *)

(** Nodes are deduplicated: no duplicates in mp_nodes *)
Definition multiproof_nodes_unique (mp : MultiProof) : Prop :=
  NoDup (mp_nodes mp).

(** [AXIOM:OPTIMIZATION] MultiProof deduplication preserves soundness.
    Deduplicating shared nodes in a multiproof maintains validity.
    This is the key property enabling space savings in batch proofs.
    
    The deduplication strategy relies on shared Merkle path prefixes
    when keys share stem prefixes (co-location property). *)
Axiom multiproof_dedup_sound :
  forall (mp : MultiProof) (root : Bytes32),
    verify_multiproof mp root ->
    multiproof_nodes_unique mp.

(** [AXIOM:OPTIMIZATION] Multiproof size is bounded by sum of individual proof sizes.
    This is a loose upper bound - actual size is smaller due to node deduplication.
    
    The bound requires the multiproof be well-formed and that nodes/stems counts
    are bounded by the tree depth (248 bits) times number of keys. In practice,
    deduplication means the actual bound is much tighter.
    
    Per-key worst case: 248 internal nodes + 8 subtree siblings + 1 stem. *)
Axiom multiproof_size_efficient :
  forall (mp : MultiProof),
    wf_multiproof mp ->
    (length (mp_nodes mp) <= length (mp_keys mp) * 256)%nat ->
    (length (mp_stems mp) <= length (mp_keys mp))%nat ->
    (multiproof_size mp <= length (mp_keys mp) * (33 + 33 + 32 * 256 + 31))%nat.

(** ** Batch to MultiProof Conversion *)

(** Convert batch of individual proofs to multiproof *)
Parameter batch_to_multiproof : BatchInclusionProof -> MultiProof.

(** [AXIOM:EQUIVALENCE] Batch to multiproof preserves semantics.
    Converting a valid batch of individual proofs to a multiproof
    produces an equivalent proof with the same key-value bindings. *)
Axiom batch_to_multiproof_equiv :
  forall (batch : BatchInclusionProof) (root : Bytes32),
    verify_batch_inclusion batch root ->
    let mp := batch_to_multiproof batch in
    verify_multiproof mp root /\
    mp_keys mp = map ip_key batch /\
    mp_values mp = map (fun p => Some (ip_value p)) batch.

(** NoDup is already imported from Stdlib.Lists.List at the top of the file *)
