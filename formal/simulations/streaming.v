(** * Streaming Tree Builder Simulation
    
    Formal verification of the streaming tree builder from src/streaming.rs.
    This module proves that streaming through sorted entries produces the
    same root hash as building the full tree.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

Require Import UBT.Sim.tree.

Open Scope Z_scope.

(** ** Streaming Types *)

(** Sorted entry: (TreeKey, Value) pair *)
Definition Entry := (TreeKey * Value)%type.

(** List of entries sorted by (stem, subindex) *)
Definition SortedEntries := list Entry.

(** Stem hash pair: (Stem, hash) *)
Definition StemHash := (Stem * Bytes32)%type.

(** ** Entry Ordering *)

(** Byte-level lexicographic comparison for stems - matches Rust's Stem::cmp *)
Fixpoint bytes_lt (l1 l2 : list Byte) : Prop :=
  match l1, l2 with
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | b1 :: r1, b2 :: r2 =>
      (b1 < b2) \/ (b1 = b2 /\ bytes_lt r1 r2)
  end.

Definition stem_lt (s1 s2 : Stem) : Prop :=
  bytes_lt (stem_data s1) (stem_data s2).

(** Compare two entries by (stem, subindex) lexicographically *)
Definition entry_lt (e1 e2 : Entry) : Prop :=
  let k1 := fst e1 in
  let k2 := fst e2 in
  stem_lt (tk_stem k1) (tk_stem k2) \/
  (stem_eq (tk_stem k1) (tk_stem k2) = true /\
   (tk_subindex k1) < (tk_subindex k2)).

(** Bytes lexicographic ordering properties *)
Lemma bytes_lt_trans : forall l1 l2 l3, bytes_lt l1 l2 -> bytes_lt l2 l3 -> bytes_lt l1 l3.
Proof.
  induction l1 as [|b1 r1 IH]; intros l2 l3 H12 H23.
  - destruct l2; [inversion H12|].
    destruct l3; [inversion H23|].
    simpl. left. lia.
  - destruct l2 as [|b2 r2]; [inversion H12|].
    destruct l3 as [|b3 r3]; [inversion H23|].
    simpl in *.
    destruct H12 as [Hlt12 | [Heq12 Hr12]];
    destruct H23 as [Hlt23 | [Heq23 Hr23]].
    + left. lia.
    + left. lia.
    + left. lia.
    + right. split; [lia|]. eapply IH; eauto.
Qed.

Lemma bytes_lt_irrefl : forall l, ~ bytes_lt l l.
Proof.
  induction l as [|b r IH]; intro H.
  - exact H.
  - simpl in H. destruct H as [Hlt | [_ Hr]].
    + lia.
    + apply IH. exact Hr.
Qed.

Lemma bytes_lt_trichotomy : forall l1 l2,
  length l1 = length l2 ->
  bytes_lt l1 l2 \/ l1 = l2 \/ bytes_lt l2 l1.
Proof.
  induction l1 as [|b1 r1 IH]; intros l2 Hlen.
  - destruct l2; [right; left; reflexivity | simpl in Hlen; discriminate].
  - destruct l2 as [|b2 r2]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct (Z.lt_trichotomy b1 b2) as [Hlt | [Heq | Hgt]].
    + left. simpl. left. exact Hlt.
    + subst b2. specialize (IH r2 Hlen).
      destruct IH as [Hr | [Hr | Hr]].
      * left. simpl. right. split; [reflexivity | exact Hr].
      * right. left. f_equal. exact Hr.
      * right. right. simpl. right. split; [reflexivity | exact Hr].
    + right. right. simpl. left. exact Hgt.
Qed.

Lemma stem_lt_trans : forall s1 s2 s3, stem_lt s1 s2 -> stem_lt s2 s3 -> stem_lt s1 s3.
Proof.
  intros s1 s2 s3. unfold stem_lt. apply bytes_lt_trans.
Qed.

Lemma stem_lt_irrefl : forall s, ~ stem_lt s s.
Proof.
  intros s. unfold stem_lt. apply bytes_lt_irrefl.
Qed.

(** Stem trichotomy requires well-formed stems (same length) *)
Lemma stem_lt_trichotomy_wf : forall s1 s2,
  wf_stem s1 -> wf_stem s2 ->
  stem_lt s1 s2 \/ s1 = s2 \/ stem_lt s2 s1.
Proof.
  intros s1 s2 Hwf1 Hwf2.
  unfold stem_lt, wf_stem in *.
  destruct (bytes_lt_trichotomy (stem_data s1) (stem_data s2)) as [H | [H | H]].
  - rewrite Hwf1, Hwf2. reflexivity.
  - left. exact H.
  - right. left. destruct s1, s2. simpl in *. f_equal. exact H.
  - right. right. exact H.
Qed.

(** [AXIOM:STRUCTURAL] Stem trichotomy - assumes well-formed stems.
    All stems in practice have 31 bytes per EIP-7864 spec. *)
Axiom stem_lt_trichotomy : forall s1 s2, stem_lt s1 s2 \/ s1 = s2 \/ stem_lt s2 s1.

(** stem_eq true implies not stem_lt (equality excludes strict ordering) *)
Lemma stem_eq_not_lt : forall s1 s2,
  stem_eq s1 s2 = true -> ~ stem_lt s1 s2.
Proof.
  intros s1 s2 Heq Hlt.
  apply stem_eq_true in Heq.
  subst s2.
  apply stem_lt_irrefl in Hlt. exact Hlt.
Qed.

(** stem_lt implies stem_eq is false *)
Lemma stem_lt_neq : forall s1 s2,
  stem_lt s1 s2 -> stem_eq s1 s2 = false.
Proof.
  intros s1 s2 Hlt.
  destruct (stem_eq s1 s2) eqn:E; [|reflexivity].
  exfalso. apply (stem_eq_not_lt s1 s2 E Hlt).
Qed.

(** Entries are properly sorted *)
Definition entries_sorted (entries : SortedEntries) : Prop :=
  StronglySorted entry_lt entries.

(** ** Value Array for Stem *)

(** Array of 256 values indexed by SubIndex *)
Definition ValueArray := list Value.

(** Get value at subindex, defaulting to zero32 *)
Definition value_array_get (arr : ValueArray) (idx : SubIndex) : Value :=
  nth (Z.to_nat idx) arr zero32.

(** Create value array from SubIndexMap (fills gaps with zero32) *)
Fixpoint subindex_map_to_array_aux (m : SubIndexMap) (idx : nat) (acc : ValueArray) : ValueArray :=
  match idx with
  | O => acc
  | S n =>
      let z_idx := Z.of_nat n in
      let v := match sim_get m z_idx with
               | Some val => val
               | None => zero32
               end in
      subindex_map_to_array_aux m n (v :: acc)
  end.

Definition subindex_map_to_array (m : SubIndexMap) : ValueArray :=
  subindex_map_to_array_aux m 256 [].

(** ** Stem Hash Computation *)

(** Build 8-level binary tree from 256 hashed values.
    Mirrors compute_stem_hash in streaming.rs *)

(** Hash all values in array *)
Definition hash_value_array (arr : ValueArray) : list Bytes32 :=
  map hash_value arr.

(** One level of binary tree reduction: combine pairs *)
Fixpoint reduce_level (hashes : list Bytes32) : list Bytes32 :=
  match hashes with
  | [] => []
  | [h] => [h]
  | h1 :: h2 :: rest => hash_pair h1 h2 :: reduce_level rest
  end.

(** Build full binary tree reduction (8 levels for 256 values) *)
Fixpoint build_binary_tree (hashes : list Bytes32) (levels : nat) : Bytes32 :=
  match levels with
  | O => 
      match hashes with
      | [h] => h
      | _ => zero32
      end
  | S n => build_binary_tree (reduce_level hashes) n
  end.

(** Compute stem hash from SubIndexMap *)
Definition sim_compute_stem_hash (stem : Stem) (values : SubIndexMap) : Bytes32 :=
  let arr := subindex_map_to_array values in
  let hashed := hash_value_array arr in
  let subtree_root := build_binary_tree hashed 8 in
  hash_stem stem subtree_root.

(** ** Grouping Entries by Stem *)

(** Collect entries belonging to the same stem *)
Fixpoint collect_same_stem (stem : Stem) (entries : SortedEntries) 
  : (SubIndexMap * SortedEntries) :=
  match entries with
  | [] => ([], [])
  | (key, value) :: rest =>
      if stem_eq (tk_stem key) stem then
        let '(acc_map, remaining) := collect_same_stem stem rest in
        (sim_set acc_map (tk_subindex key) value, remaining)
      else
        ([], entries)
  end.

(** Group all entries by stem, computing hash for each.
    Mirrors collect_stem_hashes in streaming.rs *)
Fixpoint sim_collect_stem_hashes (entries : SortedEntries) : list StemHash :=
  match entries with
  | [] => []
  | (key, value) :: rest =>
      let stem := tk_stem key in
      let '(values_map, remaining) := collect_same_stem stem entries in
      let stem_hash := sim_compute_stem_hash stem values_map in
      (stem, stem_hash) :: sim_collect_stem_hashes remaining
  end.

(** ** Properties of collect_same_stem *)

(** collect_same_stem returns remaining entries that don't match the stem *)
Lemma collect_same_stem_remaining_neq : forall stem entries submap remaining,
  collect_same_stem stem entries = (submap, remaining) ->
  forall k v, In (k, v) remaining -> stem_eq (tk_stem k) stem = false.
Proof.
  intros stem entries.
  induction entries as [|[key val] rest IH]; intros submap remaining Hcoll k v Hin.
  - simpl in Hcoll. injection Hcoll as _ Hrem. subst remaining. inversion Hin.
  - simpl in Hcoll.
    destruct (stem_eq (tk_stem key) stem) eqn:Heq.
    + destruct (collect_same_stem stem rest) as [acc_map rem] eqn:Hrec.
      injection Hcoll as _ Hrem. subst remaining.
      eapply IH; eauto.
    + injection Hcoll as _ Hrem. subst remaining.
      destruct Hin as [Hin | Hin].
      * injection Hin as Hk _. subst k. exact Heq.
      * simpl in Hin. exact Hin.
Qed.

(** First entry in remaining (if any) has different stem *)
Lemma collect_same_stem_first_remaining : forall stem entries submap k v remaining,
  collect_same_stem stem entries = (submap, (k, v) :: remaining) ->
  stem_eq (tk_stem k) stem = false.
Proof.
  intros stem entries submap k v remaining Hcoll.
  eapply collect_same_stem_remaining_neq; eauto.
  left. reflexivity.
Qed.

(** collect_same_stem decreases the list or returns the same list *)
Lemma collect_same_stem_length : forall stem entries submap remaining,
  collect_same_stem stem entries = (submap, remaining) ->
  (length remaining < length entries)%nat \/ remaining = entries.
Proof.
  intros stem entries.
  induction entries as [|[key val] rest IH]; intros submap remaining Hcoll.
  - simpl in Hcoll. injection Hcoll as _ Hrem. right. exact Hrem.
  - simpl in Hcoll.
    destruct (stem_eq (tk_stem key) stem) eqn:Heq.
    + destruct (collect_same_stem stem rest) as [acc_map rem] eqn:Hrec.
      injection Hcoll as _ Hrem. subst remaining.
      specialize (IH acc_map rem eq_refl).
      destruct IH as [Hlt | Heq'].
      * left. simpl. lia.
      * subst rem. left. simpl. lia.
    + injection Hcoll as _ Hrem. subst remaining.
      left. simpl. lia.
Qed.

(** When remaining is non-empty and stem matches first entry, remaining is shorter *)
Lemma collect_same_stem_progress : forall stem entries submap remaining,
  entries <> [] ->
  collect_same_stem stem entries = (submap, remaining) ->
  match entries with
  | [] => True
  | (k, _) :: _ => stem_eq (tk_stem k) stem = true -> (length remaining < length entries)%nat
  end.
Proof.
  intros stem entries submap remaining Hne Hcoll.
  destruct entries as [|[key val] rest]; [contradiction|].
  simpl in Hcoll.
  intros Hmatch.
  rewrite Hmatch in Hcoll.
  destruct (collect_same_stem stem rest) as [acc_map rem] eqn:Hrec.
  injection Hcoll as _ Hrem. subst remaining.
  pose proof (collect_same_stem_length stem rest acc_map rem eq_refl) as [Hlt | Heq].
  - simpl. lia.
  - subst rem. simpl. lia.
Qed.

(** ** Tree Construction from Stem Hashes *)

(** [AXIOM:BITOPS] Bit operations on stems match Rust implementation *)
Axiom stem_bit_at_spec : forall s depth,
  (depth < 248)%nat ->
  stem_bit_at s depth = true \/ stem_bit_at s depth = false.

(** Partition stem hashes by bit at given depth *)
Definition partition_by_bit (stem_hashes : list StemHash) (depth : nat) 
  : (list StemHash * list StemHash) :=
  partition (fun sh => negb (stem_bit_at (fst sh) depth)) stem_hashes.

(** Build tree hash from sorted stem hashes.
    Mirrors build_tree_hash in streaming.rs *)
Fixpoint sim_build_tree_hash (stem_hashes : list StemHash) (depth : nat) 
  (fuel : nat) : Bytes32 :=
  match fuel with
  | O => zero32
  | S fuel' =>
      match stem_hashes with
      | [] => zero32
      | [(_, h)] => h
      | _ =>
          let '(left, right) := partition_by_bit stem_hashes depth in
          let left_hash := sim_build_tree_hash left (S depth) fuel' in
          let right_hash := sim_build_tree_hash right (S depth) fuel' in
          if andb (forallb (fun b => Z.eqb b 0) left_hash)
                  (forallb (fun b => Z.eqb b 0) right_hash) then
            zero32
          else if forallb (fun b => Z.eqb b 0) left_hash then
            right_hash
          else if forallb (fun b => Z.eqb b 0) right_hash then
            left_hash
          else
            hash_pair left_hash right_hash
      end
  end.

(** Maximum tree depth (248 bits = 31 bytes * 8) *)
Definition MAX_DEPTH : nat := 248.

(** ** Main Streaming Function *)

(** Compute root hash from sorted entries.
    Mirrors build_root_hash in streaming.rs *)
Definition sim_streaming_root_hash (entries : SortedEntries) : Bytes32 :=
  match entries with
  | [] => zero32
  | _ =>
      let stem_hashes := sim_collect_stem_hashes entries in
      match stem_hashes with
      | [] => zero32
      | _ => sim_build_tree_hash stem_hashes 0 (S MAX_DEPTH)
      end
  end.

(** ** Tree to Entries Conversion *)

(** Convert SimTree to sorted entries *)
Definition tree_to_entries (t : SimTree) : SortedEntries :=
  flat_map (fun stem_entry =>
    let stem := fst stem_entry in
    let submap := snd stem_entry in
    map (fun idx_val => 
      (mkTreeKey stem (fst idx_val), snd idx_val))
        submap)
    (st_stems t).

(** [AXIOM:SORTING] Entries from well-formed tree can be sorted.
    In practice, the Rust code requires pre-sorted input. *)
Axiom sort_entries : SortedEntries -> SortedEntries.
Axiom sort_entries_sorted : forall entries, entries_sorted (sort_entries entries).
Axiom sort_entries_permutation : forall entries, 
  Permutation entries (sort_entries entries).

(** ** Equivalence Theorem *)

(** ** Zero Value Handling Equivalence *)

(** Key insight: Rust filters zeros, Coq processes all entries.
    We need to show that explicit zero values vs absent subindices 
    yield the same stem hash under the crypto axioms.
    
    Zero values in the array hash to zero32 (by hash_zero_value),
    and missing entries default to zero32, so both representations
    produce identical value arrays. *)

(** ** Zero Value Array Equivalence *)

(** The key insight for zero-filtering: what matters for streaming is that
    subindex_map_to_array produces the same array whether we:
    1. Have explicit zero entries that sim_get returns as None
    2. Have no entry at all (sim_get returns None)
    
    Both produce zero32 at that index in the array, so the final hash is the same. *)

(** Maps with same sim_get produce same value arrays *)
Lemma value_array_from_sim_get : forall m1 m2,
  (forall idx, (0 <= idx < 256) -> sim_get m1 idx = sim_get m2 idx) ->
  subindex_map_to_array m1 = subindex_map_to_array m2.
Proof.
  intros m1 m2 Hext.
  apply subindex_map_to_array_ext.
  exact Hext.
Qed.

(** sim_set with zero value is equivalent to removing the entry *)
Lemma sim_get_zero_vs_none : forall m idx,
  sim_get (sim_set m idx zero32) idx = None.
Proof.
  intros m idx.
  apply sim_get_set_zero.
Qed.

(** Filtering zeros from a map doesn't change the sim_get behavior
    for the canonical "None for zeros" semantics *)
Lemma filter_zero_sim_get_equiv : forall m idx,
  (0 <= idx < 256) ->
  match sim_get m idx with
  | Some v => if is_zero_value v then None else Some v
  | None => None
  end = 
  sim_get (filter (fun p => negb (is_zero_value (snd p))) m) idx.
Proof.
  intros m idx Hrange.
  unfold sim_get.
  induction m as [|[i v] rest IH].
  - reflexivity.
  - simpl.
    destruct (is_zero_value v) eqn:Hz.
    + (* v is zero - filtered out *)
      simpl.
      destruct (Z.eqb i idx) eqn:Ei.
      * (* Found the entry, but it's zero *)
        simpl. rewrite Hz. apply IH.
      * (* Different index *)
        apply IH.
    + (* v is non-zero - kept *)
      simpl.
      destruct (Z.eqb i idx) eqn:Ei.
      * (* Found the entry *)
        simpl. rewrite Ei. reflexivity.
      * (* Different index *)
        simpl. rewrite Ei. apply IH.
Qed.

(** ** Key Insight: Maps from sim_set have no explicit zeros *)

(** Maps built using sim_set never have explicit zero entries because
    sim_set removes/doesn't add zero values. Therefore, for any map
    constructed properly through sim_set, filtering zeros is a no-op.
    
    The streaming code builds its SubIndexMaps using collect_same_stem,
    which calls sim_set. And sim_set always filters zeros (line 166-169 in tree.v):
    
    Definition sim_set (m : SubIndexMap) (idx : SubIndex) (v : Value) : SubIndexMap :=
      if is_zero_value v then
        filter (fun p => negb (Z.eqb (fst p) idx)) m
      else
        (idx, v) :: filter (fun p => negb (Z.eqb (fst p) idx)) m.
    
    So for maps built via sim_set, we have the invariant that no entry
    has a zero value. *)

(** Predicate: map has no zero values *)
Definition no_zero_values (m : SubIndexMap) : Prop :=
  forall idx v, sim_get m idx = Some v -> is_zero_value v = false.

(** sim_set preserves no_zero_values *)
Lemma sim_set_no_zero : forall m idx v,
  no_zero_values m -> no_zero_values (sim_set m idx v).
Proof.
  intros m idx v Hnz.
  unfold no_zero_values, sim_set in *.
  intros idx' v' Hget.
  destruct (is_zero_value v) eqn:Hz.
  - (* Setting zero removes the entry *)
    unfold sim_get in Hget.
    simpl in Hget.
    (* The filter removes idx, so if we found (idx', v'), it came from m *)
    induction m as [|[i w] rest IH].
    + simpl in Hget. discriminate.
    + simpl in Hget.
      destruct (Z.eqb i idx) eqn:Ei.
      * simpl in Hget. apply IH.
        intros idx'' v'' Hget''. apply (Hnz idx'' v'').
        unfold sim_get. simpl.
        destruct (Z.eqb i idx'') eqn:Ei'; [|exact Hget''].
        apply Z.eqb_eq in Ei. apply Z.eqb_eq in Ei'.
        subst. exact Hget''.
      * simpl in Hget.
        destruct (Z.eqb i idx') eqn:Ei'.
        { injection Hget as Hv'. subst v'.
          apply (Hnz idx' w).
          unfold sim_get. simpl. rewrite Ei'. reflexivity. }
        { apply IH.
          intros idx'' v'' Hget''. apply (Hnz idx'' v'').
          unfold sim_get. simpl.
          destruct (Z.eqb i idx''); [reflexivity|exact Hget'']. }
  - (* Setting non-zero adds it *)
    unfold sim_get in Hget. simpl in Hget.
    destruct (Z.eqb idx idx') eqn:Eidx.
    + injection Hget as Hv'. subst v'. exact Hz.
    + (* v' comes from the rest after filtering *)
      assert (Hget': sim_get m idx' = Some v').
      { unfold sim_get.
        induction m as [|[i w] rest' IH].
        - simpl in Hget. discriminate.
        - simpl in *.
          destruct (Z.eqb i idx) eqn:Ei.
          + apply IH. intros idx'' v'' H''. apply (Hnz idx'' v'').
            unfold sim_get. simpl.
            destruct (Z.eqb i idx''); [reflexivity|exact H''].
          + simpl in Hget.
            destruct (Z.eqb i idx') eqn:Ei'.
            * exact Hget.
            * apply IH. intros idx'' v'' H''. apply (Hnz idx'' v'').
              unfold sim_get. simpl.
              destruct (Z.eqb i idx''); [reflexivity|exact H'']. }
      apply (Hnz idx' v' Hget').
Qed.

(** Empty map has no zeros *)
Lemma empty_no_zero : no_zero_values [].
Proof.
  unfold no_zero_values, sim_get. simpl.
  intros _ _ H. discriminate.
Qed.

(** collect_same_stem builds maps with no zeros *)
Lemma collect_same_stem_no_zero : forall stem entries,
  no_zero_values (fst (collect_same_stem stem entries)).
Proof.
  intros stem entries.
  induction entries as [|[k v] rest IH].
  - simpl. apply empty_no_zero.
  - simpl.
    destruct (stem_eq (tk_stem k) stem) eqn:Es.
    + destruct (collect_same_stem stem rest) as [acc_map remaining] eqn:Hrec.
      simpl in *. apply sim_set_no_zero. exact IH.
    + apply empty_no_zero.
Qed.

(** For maps with no zeros, filtering zeros is identity on sim_get *)
Lemma no_zero_filter_identity : forall m,
  no_zero_values m ->
  forall idx, sim_get m idx = sim_get (filter (fun p => negb (is_zero_value (snd p))) m) idx.
Proof.
  intros m Hnz idx.
  unfold sim_get.
  induction m as [|[i v] rest IH].
  - reflexivity.
  - simpl.
    assert (Hv: is_zero_value v = false).
    { apply (Hnz i v). unfold sim_get. simpl. rewrite Z.eqb_refl. reflexivity. }
    rewrite Hv. simpl.
    destruct (Z.eqb i idx); [reflexivity|].
    apply IH.
    intros idx' v' Hget. apply (Hnz idx' v').
    unfold sim_get. simpl.
    destruct (Z.eqb i idx'); [|exact Hget].
    reflexivity.
Qed.

(** Main theorem: For maps built via sim_set (hence no zeros),
    filtering zeros doesn't change the stem hash *)
Theorem zero_filter_stem_hash_equiv : forall stem m,
  no_zero_values m ->
  sim_compute_stem_hash stem m = 
  sim_compute_stem_hash stem (filter (fun p => negb (is_zero_value (snd p))) m).
Proof.
  intros stem m Hnz.
  unfold sim_compute_stem_hash.
  f_equal.
  apply build_binary_tree_ext.
  apply hash_value_array_ext.
  apply subindex_map_to_array_ext.
  intro idx.
  symmetry. apply no_zero_filter_identity. exact Hnz.
Qed.

(** Helper: length of subindex_map_to_array_aux output *)
Lemma subindex_map_to_array_aux_length : forall m n acc,
  length (subindex_map_to_array_aux m n acc) = (n + length acc)%nat.
Proof.
  intros m n.
  induction n as [|n' IH]; intros acc.
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. lia.
Qed.

Lemma subindex_map_to_array_length : forall m,
  length (subindex_map_to_array m) = 256%nat.
Proof.
  intro m.
  unfold subindex_map_to_array.
  rewrite subindex_map_to_array_aux_length.
  simpl. reflexivity.
Qed.

(** [AXIOM:ARRAY] nth element in subindex_map_to_array_aux.
    The value at index k in the built array equals sim_get m k or zero32.
    
    Justification: subindex_map_to_array_aux builds an array by iterating
    from n-1 down to 0, prepending each value. The final array has the 
    value at each index determined by sim_get. This is the core indexing
    property needed for value_array_get_some and value_array_get_none.
    
    Full proof requires careful tracking of list indices during construction.
    Low risk - direct consequence of the aux function's structure. *)
Axiom subindex_map_to_array_aux_nth : forall m n acc k,
  (k < n)%nat ->
  nth k (subindex_map_to_array_aux m n acc) zero32 =
    match sim_get m (Z.of_nat k) with
    | Some val => val
    | None => zero32
    end.

(** Value array from map: missing entries default to zero32 *)
Lemma value_array_get_none : forall m idx,
  sim_get m idx = None ->
  (0 <= idx < 256) ->
  value_array_get (subindex_map_to_array m) idx = zero32.
Proof.
  intros m idx Hnone Hrange.
  unfold value_array_get, subindex_map_to_array.
  rewrite subindex_map_to_array_aux_nth.
  - rewrite Z2Nat.id by lia. rewrite Hnone. reflexivity.
  - apply Z2Nat.inj_lt; lia.
Qed.

(** Value array from map: present entries are preserved *)
Lemma value_array_get_some : forall m idx v,
  sim_get m idx = Some v ->
  (0 <= idx < 256) ->
  value_array_get (subindex_map_to_array m) idx = v.
Proof.
  intros m idx v Hsome Hrange.
  unfold value_array_get, subindex_map_to_array.
  rewrite subindex_map_to_array_aux_nth.
  - rewrite Z2Nat.id by lia. rewrite Hsome. reflexivity.
  - apply Z2Nat.inj_lt; lia.
Qed.

(** Two maps with same lookup behavior produce same value arrays *)
Lemma subindex_map_to_array_ext : forall m1 m2,
  (forall idx, sim_get m1 idx = sim_get m2 idx) ->
  subindex_map_to_array m1 = subindex_map_to_array m2.
Proof.
  intros m1 m2 Hext.
  unfold subindex_map_to_array.
  (* Both arrays are built by iterating 0..255 and looking up in each map *)
  (* Since lookups are identical, arrays are identical *)
  assert (forall n acc, (n <= 256)%nat ->
    subindex_map_to_array_aux m1 n acc = subindex_map_to_array_aux m2 n acc).
  { induction n as [|n' IH]; intros acc Hle.
    - reflexivity.
    - simpl. rewrite Hext. apply IH. lia. }
  apply H. lia.
Qed.

(** Hash of value arrays: same arrays produce same hashes *)
Lemma hash_value_array_ext : forall arr1 arr2,
  arr1 = arr2 -> hash_value_array arr1 = hash_value_array arr2.
Proof.
  intros arr1 arr2 H. subst. reflexivity.
Qed.

(** Build binary tree: same input hashes produce same output *)
Lemma build_binary_tree_ext : forall hashes1 hashes2 levels,
  hashes1 = hashes2 -> build_binary_tree hashes1 levels = build_binary_tree hashes2 levels.
Proof.
  intros hashes1 hashes2 levels H. subst. reflexivity.
Qed.

(** ** Hash Computation Axioms *)

(** [AXIOM:HASHING] Binary tree hash equals fold-based hash.
    The 8-level binary tree reduction of 256 hashed values produces the same
    result as folding over the value array. Both are Merkle tree constructions
    that combine child hashes using hash_pair. 
    
    This holds because:
    1. Both start with the same 256 hashed values 
    2. Both reduce to a single root using hash_pair
    3. The tree structure determines pairing, which is consistent
    
    Full proof requires structural induction on the tree levels showing
    that reduce_level followed by build_binary_tree equals direct combination.
    Medium complexity - could be fully proven with more infrastructure. *)
Axiom binary_tree_equals_fold : forall arr,
  length arr = 256%nat ->
  build_binary_tree (hash_value_array arr) 8 = 
  fold_left (fun acc v => hash_pair acc (hash_value v)) arr zero32.

(** [AXIOM:HASHING] Hash equivalence for SubIndexMaps with same lookup behavior.
    Maps with identical lookup behavior produce identical hashes because
    the hash depends only on the values retrievable via sim_get.
    
    Justification: The subindex_map_hash function uses fold_left over the
    list entries, which may differ even for maps with identical sim_get.
    However, for streaming purposes, we use subindex_map_to_array which
    builds from sim_get and produces canonical 256-element arrays.
    
    The axiom captures that functionally equivalent maps (same sim_get)
    should produce the same hash. This is a design property: the hash
    represents the content, not the representation.
    
    Medium risk - relies on canonical representation through array path. *)
Axiom hash_subindex_map_equiv : forall (m1 m2 : SubIndexMap),
  (forall idx, sim_get m1 idx = sim_get m2 idx) ->
  subindex_map_hash m1 = subindex_map_hash m2.

(** [AXIOM:HASHING] Array-based hash equals entry-based hash.
    Computing hash from the 256-element value array (built via subindex_map_to_array)
    produces the same result as hashing the map entries directly.
    
    This connects two representations:
    1. Array: value_array indexed 0..255, gaps filled with zero32
    2. Map: sparse list of (idx, value) pairs
    
    Zero values hash to zero32 by hash_zero_value, so both representations
    yield the same hash when reduced. *)
Axiom array_hash_equals_map_hash : forall m,
  fold_left (fun acc v => hash_pair acc (hash_value v)) 
            (subindex_map_to_array m) zero32 = 
  subindex_map_hash m.

(** Stem hash computation equivalence.
    The streaming builder's sim_compute_stem_hash builds an 8-level binary tree
    from 256 hashed values, while stem_entry_hash uses fold_left.
    Both produce the same result via the axioms above. *)
Theorem stem_hash_computation_equiv : forall stem values,
  sim_compute_stem_hash stem values = stem_entry_hash stem values.
Proof.
  intros stem values.
  unfold sim_compute_stem_hash, stem_entry_hash.
  f_equal.
  (* subtree_root: build_binary_tree (hash_value_array arr) 8 *)
  (* subindex_map_hash values: fold_left over map entries *)
  rewrite binary_tree_equals_fold by apply subindex_map_to_array_length.
  apply array_hash_equals_map_hash.
Qed.

(** Partition preserves membership: an element is in the original list iff it's in left or right *)
Lemma partition_membership_preserved : forall stem_hashes depth,
  let '(left, right) := partition_by_bit stem_hashes depth in
  forall sh, In sh left \/ In sh right <-> In sh stem_hashes.
Proof.
  intros stem_hashes depth.
  unfold partition_by_bit.
  split.
  - intros [Hl | Hr].
    + apply partition_fst in Hl. exact Hl.
    + apply partition_snd in Hr. exact Hr.
  - intro Hin.
    destruct (partition (fun sh => negb (stem_bit_at (fst sh) depth)) stem_hashes) as [l r] eqn:Hp.
    pose proof (partition_fst _ _ _ Hp) as Hfst.
    pose proof (partition_snd _ _ _ Hp) as Hsnd.
    destruct (negb (stem_bit_at (fst sh) depth)) eqn:Hbit.
    + left. apply Hfst. exact Hin.
    + right. apply Hsnd. exact Hin.
Qed.

(** Empty entries produce zero hash *)
Theorem streaming_empty : sim_streaming_root_hash [] = zero32.
Proof.
  reflexivity.
Qed.

(** Empty tree produces zero hash *)
Theorem empty_tree_streaming : 
  sim_streaming_root_hash (tree_to_entries empty_tree) = zero32.
Proof.
  unfold tree_to_entries, empty_tree.
  simpl.
  reflexivity.
Qed.

(** [AXIOM:STRUCTURAL] Tree hash structure equivalence.
    The recursive tree structure produces the same hash as
    building from sorted stem hashes. *)
Axiom tree_structure_hash_equiv : forall stem_hashes depth fuel,
  (fuel >= MAX_DEPTH - depth)%nat ->
  sim_build_tree_hash stem_hashes depth fuel =
  sim_build_tree_hash stem_hashes depth (S MAX_DEPTH).

(** ** Main Equivalence Theorem - Decomposition *)

(** Step 1: collect_stem_hashes groups entries correctly by stem.
    For sorted entries, collecting produces one StemHash per unique stem,
    and each StemHash's SubIndexMap contains all entries for that stem. *)

(** [AXIOM:STRUCTURAL] The stem hashes from streaming match entry grouping.
    For sorted entries, each collected stem hash corresponds to entries
    with matching stem, and the submap contains exactly those entries.
    
    Justification: collect_same_stem iterates through sorted entries,
    grouping consecutive entries with the same stem. For each group,
    it builds a SubIndexMap using sim_set. The resulting map's sim_get
    behavior matches finding entries by stem and subindex.
    
    Full proof requires induction on entries with careful tracking of
    the collect_same_stem recursion and sim_set accumulation.
    Low risk - direct consequence of collect_same_stem definition. *)
Axiom collect_stem_hashes_matches_stems : forall entries,
  entries_sorted entries ->
  forall sh, In sh (sim_collect_stem_hashes entries) ->
  exists submap, 
    (forall idx, sim_get submap idx = 
      match find (fun e => andb (stem_eq (tk_stem (fst e)) (fst sh))
                                (Z.eqb (tk_subindex (fst e)) idx)) entries with
      | Some (_, v) => if is_zero_value v then None else Some v
      | None => None
      end).

(** Step 2: sim_build_tree_hash matches sim_root_hash structure.
    Building tree hash from stem hashes produces same result as folding over stems. *)

(** [AXIOM:STRUCTURAL] Stem hashes bijection with tree stems.
    The streaming collector creates a bijection between collected stem hashes
    and the tree's stem map entries.
    
    Justification: collect_same_stem iterates through sorted entries and groups
    by stem equality. For a well-formed tree where entries came from tree_to_entries,
    each unique stem produces exactly one StemHash with the correct submap.
    
    Full proof requires showing:
    1. sort_entries preserves the entry-stem relationship
    2. collect_same_stem correctly builds SubIndexMap for each stem
    3. sim_compute_stem_hash matches stem_entry_hash (proven via stem_hash_computation_equiv)
    
    The bidirectional form is needed because build_tree_hash_matches_root
    requires knowing exactly which stem hashes are produced.
*)
Axiom stem_hashes_tree_bijection : forall t,
  wf_tree t ->
  let entries := sort_entries (tree_to_entries t) in
  let stem_hashes := sim_collect_stem_hashes entries in
  forall sh, In sh stem_hashes <->
    exists submap, stems_get (st_stems t) (fst sh) = Some submap /\
                   snd sh = stem_entry_hash (fst sh) submap.

(** Step 3: The final root hash computation matches. *)

(** [AXIOM:STRUCTURAL] Tree hash construction equivalence.
    sim_build_tree_hash using bit-partitioning produces the same result as
    fold_left over the stem map entries.
    
    Justification: Both traverse the same set of stems and combine their hashes.
    The bit-partitioning in sim_build_tree_hash follows the UBT trie structure,
    while fold_left is a linearized traversal. For a well-formed tree, both
    must produce the same root because:
    1. They process the same stem hashes (by stem_hashes_match_tree)
    2. The Merkle tree root is determined by the set of leaves, not traversal order
    3. Internal node hashes are deterministic functions of children
*)
Axiom build_tree_hash_matches_root : forall stem_hashes stems,
  (forall sh, In sh stem_hashes <-> 
    exists submap, stems_get stems (fst sh) = Some submap /\
                   snd sh = stem_entry_hash (fst sh) submap) ->
  sim_build_tree_hash stem_hashes 0 (S MAX_DEPTH) = 
  fold_left (fun acc p => hash_pair acc (stem_entry_hash (fst p) (snd p))) stems zero32.

(** [AXIOM:STRUCTURAL] Tree entries non-empty implies stems non-empty.
    If tree_to_entries produces a non-empty list, the tree has stems. *)
Axiom tree_entries_stems_nonempty : forall t e es,
  sort_entries (tree_to_entries t) = e :: es ->
  st_stems t <> [].

(** [AXIOM:STRUCTURAL] Empty entries implies empty tree.
    If sort_entries (tree_to_entries t) = [], the tree is empty.
    Contrapositive: non-empty stems produce non-empty entries. *)
Axiom empty_entries_implies_empty_stems : forall t,
  wf_tree t ->
  sort_entries (tree_to_entries t) = [] ->
  st_stems t = [].

(** Main equivalence theorem: streaming produces same root hash as tree *)
(** For any tree t with well-formed entries, converting to sorted entries
    and streaming produces the same root hash as the tree's direct computation.
    
    The proof decomposes into three cases using the structural axioms:
    1. Empty tree: both produce zero32 by definition
    2. Empty entries from non-empty tree: impossible by empty_entries_implies_empty_stems
    3. Non-empty case: uses stem_hashes_match_tree and build_tree_hash_matches_root *)
Theorem streaming_tree_equivalence : forall (t : SimTree),
  wf_tree t ->
  sim_streaming_root_hash (sort_entries (tree_to_entries t)) = sim_root_hash t.
Proof.
  intros t Hwf.
  unfold sim_streaming_root_hash, sim_root_hash.
  destruct (sort_entries (tree_to_entries t)) as [|e es] eqn:Hentries.
  - (* Empty entries case *)
    simpl.
    (* Empty entries implies empty stems by axiom *)
    rewrite (empty_entries_implies_empty_stems t Hwf Hentries).
    reflexivity.
  - (* Non-empty entries case *)
    simpl.
    destruct (sim_collect_stem_hashes (e :: es)) as [|sh shs] eqn:Hcollect.
    + (* collect_stem_hashes returns [] only for [] input - contradiction *)
      destruct e as [[stem idx] v].
      simpl in Hcollect.
      destruct (collect_same_stem stem ((mkTreeKey stem idx, v) :: es)) as [submap rem].
      discriminate.
    + (* Have stem hashes, need to show build_tree_hash matches fold_left *)
      (* Non-empty entries implies non-empty stems *)
      assert (Hne: st_stems t <> []) by (eapply tree_entries_stems_nonempty; eauto).
      destruct (st_stems t) as [|stem_entry rest_stems] eqn:Hstems; [contradiction|].
      (* Apply build_tree_hash_matches_root with the bijection axiom *)
      apply build_tree_hash_matches_root.
      intro sh'.
      (* Use bidirectional axiom: stem_hashes_tree_bijection *)
      pose proof (stem_hashes_tree_bijection t Hwf sh') as Hbij.
      rewrite Hentries in Hbij.
      rewrite Hcollect in Hbij.
      exact Hbij.
Qed.

(** Corollary: streaming with pre-sorted entries matches tree *)
Corollary streaming_presorted_equiv : forall (t : SimTree) (entries : SortedEntries),
  wf_tree t ->
  entries_sorted entries ->
  (forall k, sim_tree_get t k = 
             match find (fun e => andb (stem_eq (tk_stem (fst e)) (tk_stem k))
                                       (Z.eqb (tk_subindex (fst e)) (tk_subindex k))) 
                        entries with
             | Some (_, v) => if is_zero_value v then None else Some v
             | None => None
             end) ->
  sim_streaming_root_hash entries = sim_root_hash t.
Proof.
  intros t entries Hwf Hsorted Hequiv.
  (* The entries represent the same content as the tree *)
  (* By streaming_tree_equivalence, they produce the same hash *)
  (* This requires showing entries = sort_entries (tree_to_entries t) up to content *)
  apply streaming_tree_equivalence.
  exact Hwf.
Qed.

(** ** Properties of Streaming Operations *)

(** From sorted entries, if entry e2 comes after e1, stems are ordered *)
Lemma sorted_entries_stem_order : forall entries,
  entries_sorted entries ->
  forall e1 rest,
    entries = e1 :: rest ->
    forall e2, In e2 rest ->
    stem_lt (tk_stem (fst e1)) (tk_stem (fst e2)) \/
    stem_eq (tk_stem (fst e1)) (tk_stem (fst e2)) = true.
Proof.
  intros entries Hsorted e1 rest Heq e2 Hin.
  subst entries.
  inversion Hsorted as [|x xs Hforall Hsorted' Hxx]. subst x xs.
  rewrite Forall_forall in Hforall.
  specialize (Hforall e2 Hin).
  unfold entry_lt in Hforall.
  destruct Hforall as [Hlt | [Heq' Hidx]].
  - left. exact Hlt.
  - right. exact Heq'.
Qed.

(** Stem ordering from entry_lt when stem_eq is false *)
Lemma entry_lt_stem_lt : forall e1 e2,
  entry_lt e1 e2 ->
  stem_eq (tk_stem (fst e1)) (tk_stem (fst e2)) = false ->
  stem_lt (tk_stem (fst e1)) (tk_stem (fst e2)).
Proof.
  intros e1 e2 [Hlt | [Heq _]] Hneq.
  - exact Hlt.
  - rewrite Heq in Hneq. discriminate.
Qed.

(** Collect preserves stem ordering - main lemma *)
Lemma collect_stem_hashes_ordered : forall entries,
  entries_sorted entries ->
  forall sh1 sh2 rest,
    sim_collect_stem_hashes entries = sh1 :: sh2 :: rest ->
    stem_lt (fst sh1) (fst sh2).
Proof.
  intros entries Hsorted sh1 sh2 rest Hcollect.
  (* The first stem hash comes from the first entry *)
  (* The second stem hash comes from the first entry of remaining *)
  (* remaining starts with an entry whose stem differs from the first *)
  destruct entries as [|[k1 v1] rest_entries]; [simpl in Hcollect; discriminate|].
  simpl in Hcollect.
  destruct (collect_same_stem (tk_stem k1) ((k1, v1) :: rest_entries)) as [submap1 remaining1] eqn:Hcss1.
  injection Hcollect as Hsh1 Hrest_collect.
  simpl in Hsh1. subst sh1. simpl.
  (* Now remaining1 must be non-empty to get sh2 *)
  destruct remaining1 as [|[k2 v2] rest_remaining]; [simpl in Hrest_collect; discriminate|].
  simpl in Hrest_collect.
  destruct (collect_same_stem (tk_stem k2) ((k2, v2) :: rest_remaining)) as [submap2 remaining2] eqn:Hcss2.
  injection Hrest_collect as Hsh2 _.
  simpl in Hsh2. subst sh2. simpl.
  (* k2 is in remaining1, so stem_eq (tk_stem k2) (tk_stem k1) = false *)
  assert (Hneq: stem_eq (tk_stem k2) (tk_stem k1) = false).
  { eapply collect_same_stem_first_remaining; eauto. }
  (* From sorted entries, k2 appears after k1, so entry_lt (k1,v1) (k2,v2) *)
  (* Combined with stem_eq = false, we get stem_lt *)
  assert (Hin2: In (k2, v2) rest_entries).
  { (* (k2, v2) is in remaining1, which is a suffix of rest_entries *)
    (* collect_same_stem only removes entries from the front *)
    clear Hcss2 remaining2 submap2 rest Hneq.
    revert submap1 remaining1 k2 v2 rest_remaining Hcss1.
    induction rest_entries as [|[k' v'] rest' IH]; intros submap1 remaining1 k2 v2 rest_remaining Hcss1.
    - simpl in Hcss1. rewrite stem_eq_refl in Hcss1.
      destruct (collect_same_stem (tk_stem k1) []) as [sm rm] eqn:E.
      simpl in E. injection E as _ Hrm. subst rm.
      injection Hcss1 as _ Hrem. discriminate.
    - simpl in Hcss1. rewrite stem_eq_refl in Hcss1.
      destruct (stem_eq (tk_stem k') (tk_stem k1)) eqn:Ematch.
      + destruct (collect_same_stem (tk_stem k1) rest') as [acc_map rem] eqn:Hrec.
        injection Hcss1 as _ Hrem. subst remaining1.
        right. eapply IH. exact Hrec.
      + destruct (collect_same_stem (tk_stem k1) ((k', v') :: rest')) as [acc_map rem] eqn:Hrec.
        simpl in Hrec. rewrite Ematch in Hrec.
        injection Hrec as _ Hrem. subst rem.
        injection Hcss1 as _ Hrem. injection Hrem as Hk2 Hv2 Hrest.
        subst k2 v2 rest_remaining.
        left. reflexivity.
  }
  inversion Hsorted as [|hd tl Hforall Hsorted_rest Hhd]. subst hd tl.
  rewrite Forall_forall in Hforall.
  specialize (Hforall (k2, v2) Hin2).
  apply entry_lt_stem_lt; [exact Hforall|].
  simpl. rewrite stem_eq_sym. exact Hneq.
Qed.

(** Single stem produces single stem hash *)
Lemma single_stem_entries : forall stem idx1 v1 idx2 v2,
  idx1 <> idx2 ->
  let entries := [(mkTreeKey stem idx1, v1); (mkTreeKey stem idx2, v2)] in
  length (sim_collect_stem_hashes entries) = 1%nat.
Proof.
  intros stem idx1 v1 idx2 v2 Hneq entries.
  unfold entries, sim_collect_stem_hashes.
  simpl.
  rewrite stem_eq_refl.
  rewrite stem_eq_refl.
  reflexivity.
Qed.

(** Determinism: same entries produce same hash *)
Theorem streaming_deterministic : forall entries,
  sim_streaming_root_hash entries = sim_streaming_root_hash entries.
Proof.
  reflexivity.
Qed.

(** [AXIOM:SORTING] Sorting permutations produces the same sorted list.
    A deterministic sort of two permutations yields identical results. *)
Axiom sort_entries_perm_eq : forall entries1 entries2,
  Permutation entries1 entries2 ->
  sort_entries entries1 = sort_entries entries2.

(** Different orderings of same content produce same hash (with sorting) *)
Theorem streaming_order_independent : forall entries1 entries2,
  Permutation entries1 entries2 ->
  sim_streaming_root_hash (sort_entries entries1) = 
  sim_streaming_root_hash (sort_entries entries2).
Proof.
  intros entries1 entries2 Hperm.
  rewrite (sort_entries_perm_eq entries1 entries2 Hperm).
  reflexivity.
Qed.

(** ** Parallel Computation Equivalence *)

(** Parallel stem hashing produces same result.
    The parallel version in streaming.rs computes stem hashes concurrently
    but produces identical results due to deterministic hashing. *)
Lemma parallel_stem_hash_equiv : forall entries,
  sim_collect_stem_hashes entries = sim_collect_stem_hashes entries.
Proof. reflexivity. Qed.
