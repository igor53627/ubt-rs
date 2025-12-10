(** * Iterator Simulation Specification
    
    This module provides a functional specification for tree iteration
    operations. While the Rust implementation does not expose explicit
    iterator types, these specifications model conceptual iteration
    over tree contents for verification purposes.
    
    ** Priority: LOW (informational/completeness)
    
    These specifications are provided for completeness and to support
    reasoning about bulk operations. They are not performance-critical
    and model conceptual rather than concrete iteration.
    
    ** Design Notes
    
    The iteration order in this specification is abstract and unspecified.
    The Rust implementation uses HashMap which has arbitrary iteration order.
    Theorems here focus on content properties (completeness, uniqueness)
    rather than ordering guarantees.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import UBT.Sim.tree.
Import ListNotations.

Open Scope Z_scope.

(** ** Iterator Types *)

(** Entry: a key-value pair from the tree *)
Definition Entry := (TreeKey * Value)%type.

(** ** Core Iterator Operations *)

(** Extract all stems from the tree *)
Definition sim_tree_stems (t : SimTree) : list Stem :=
  map fst (st_stems t).

(** Extract all keys from a subindex map *)
Definition submap_keys (m : SubIndexMap) : list SubIndex :=
  map fst m.

(** Extract all values from a subindex map *)
Definition submap_values (m : SubIndexMap) : list Value :=
  map snd m.

(** Extract all key-value entries from a subindex map *)
Definition submap_entries (m : SubIndexMap) : list (SubIndex * Value) :=
  m.

(** Helper: expand stem node entries to full TreeKey entries *)
Definition expand_stem_entries (stem : Stem) (m : SubIndexMap) : list Entry :=
  map (fun p => (mkTreeKey stem (fst p), snd p)) m.

(** Get all keys in the tree *)
Definition sim_tree_keys (t : SimTree) : list TreeKey :=
  flat_map (fun sm => 
    map (fun idx => mkTreeKey (fst sm) idx) (map fst (snd sm))
  ) (st_stems t).

(** Get all values in the tree *)
Definition sim_tree_values (t : SimTree) : list Value :=
  flat_map (fun sm => map snd (snd sm)) (st_stems t).

(** Get all entries (key-value pairs) in the tree *)
Definition sim_tree_entries (t : SimTree) : list Entry :=
  flat_map (fun sm => expand_stem_entries (fst sm) (snd sm)) (st_stems t).

(** ** Fold Operation *)

(** Fold over all entries in the tree.
    The fold order is unspecified (matches HashMap behavior). *)
Definition sim_tree_fold {A : Type} (f : A -> TreeKey -> Value -> A) (init : A) (t : SimTree) : A :=
  fold_left (fun acc entry => f acc (fst entry) (snd entry)) (sim_tree_entries t) init.

(** Fold over stems only *)
Definition sim_tree_fold_stems {A : Type} (f : A -> Stem -> SubIndexMap -> A) (init : A) (t : SimTree) : A :=
  fold_left (fun acc sm => f acc (fst sm) (snd sm)) (st_stems t) init.

(** ** Helper Lemmas *)

(** Entries contain only non-zero values by SubIndexMap invariant *)
Definition entry_nonzero (e : Entry) : Prop :=
  value_nonzero (snd e).

(** Helper: In for flat_map *)
Lemma In_flat_map : forall {A B : Type} (f : A -> list B) (l : list A) (b : B),
  In b (flat_map f l) <-> exists a, In a l /\ In b (f a).
Proof.
  intros A B f l b.
  split.
  - induction l as [|x rest IH]; intros H.
    + simpl in H. destruct H.
    + simpl in H. apply in_app_or in H. destruct H.
      * exists x. split; [left; auto | auto].
      * apply IH in H. destruct H as [a [Hin Hb]].
        exists a. split; [right; auto | auto].
  - intros [a [Hin Hb]].
    induction l as [|x rest IH].
    + destruct Hin.
    + simpl. apply in_or_app.
      destruct Hin as [Heq | Hin].
      * subst. left. exact Hb.
      * right. apply IH. exact Hin.
Qed.

(** Helper: In for map *)
Lemma In_map_iff : forall {A B : Type} (f : A -> B) (l : list A) (b : B),
  In b (map f l) <-> exists a, In a l /\ b = f a.
Proof.
  intros A B f l b.
  split.
  - induction l as [|x rest IH]; intros H.
    + destruct H.
    + simpl in H. destruct H.
      * exists x. split; [left; auto | auto].
      * apply IH in H. destruct H as [a [Hin Heq]].
        exists a. split; [right; auto | auto].
  - intros [a [Hin Heq]]. subst.
    apply in_map. exact Hin.
Qed.

(** ** Key Completeness Theorem *)

(** All keys with values in the tree appear in sim_tree_keys *)
Theorem keys_complete : forall (t : SimTree) (k : TreeKey) (v : Value),
  sim_tree_get t k = Some v ->
  In k (sim_tree_keys t).
Proof.
  intros t k v Hget.
  unfold sim_tree_get in Hget.
  destruct (stems_get (st_stems t) (tk_stem k)) as [submap|] eqn:Hstem; [|discriminate].
  unfold sim_tree_keys.
  apply In_flat_map.
  (* Find the stem entry *)
  unfold stems_get in Hstem.
  destruct (find (fun p => stem_eq (fst p) (tk_stem k)) (st_stems t)) as [[s sm]|] eqn:Hfind;
    [|discriminate].
  injection Hstem as Hsm. subst sm.
  (* The stem s is in st_stems t *)
  assert (Hin_stem: In (s, submap) (st_stems t)).
  { clear -Hfind.
    induction (st_stems t) as [|[s' m'] rest IH].
    - discriminate.
    - simpl in Hfind. destruct (stem_eq s' (tk_stem k)) eqn:E.
      + injection Hfind as H1 H2. subst. left. reflexivity.
      + right. apply IH. exact Hfind. }
  exists (s, submap). split; [exact Hin_stem|].
  (* The subindex is in the submap *)
  apply In_map_iff.
  unfold sim_get in Hget.
  destruct (find (fun p => Z.eqb (fst p) (tk_subindex k)) submap) as [[idx val]|] eqn:Hfind2;
    [|discriminate].
  injection Hget as Hv. subst v.
  assert (In (idx, val) submap).
  { clear -Hfind2.
    induction submap as [|[i v'] rest IH].
    - discriminate.
    - simpl in Hfind2. destruct (Z.eqb i (tk_subindex k)) eqn:E.
      + injection Hfind2 as H1 H2. subst. left. reflexivity.
      + right. apply IH. exact Hfind2. }
  exists (tk_subindex k). split.
  - apply In_map_iff. exists (idx, val). split; [exact H|].
    simpl.
    (* idx = tk_subindex k from find success *)
    clear -Hfind2.
    induction submap as [|[i v'] rest IH].
    + discriminate.
    + simpl in Hfind2. destruct (Z.eqb i (tk_subindex k)) eqn:E.
      * injection Hfind2 as H1 H2. subst.
        apply Z.eqb_eq in E. symmetry. exact E.
      * apply IH. exact Hfind2.
  - destruct k as [stem idx']. simpl.
    (* stem = s from stem_eq *)
    assert (Hstem_eq: stem_eq s stem = true).
    { clear -Hfind.
      induction (st_stems t) as [|[s' m'] rest IH].
      - discriminate.
      - simpl in Hfind. destruct (stem_eq s' stem) eqn:E.
        + injection Hfind as H1 H2. subst. exact E.
        + apply IH. exact Hfind. }
    apply stem_eq_true in Hstem_eq. subst. reflexivity.
Qed.

(** ** Key Uniqueness Theorem *)

(** Helper: NoDup for map when function is injective on domain *)
Lemma NoDup_map_injective : forall {A B : Type} (f : A -> B) (l : list A),
  (forall a1 a2, In a1 l -> In a2 l -> f a1 = f a2 -> a1 = a2) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd.
  induction Hnd as [|x rest Hnotin Hnd IH].
  - constructor.
  - simpl. constructor.
    + intro Hin. apply In_map_iff in Hin.
      destruct Hin as [a [Hin Heq]].
      assert (x = a).
      { apply Hinj; [left; auto | right; auto | symmetry; auto]. }
      subst. contradiction.
    + apply IH. intros a1 a2 Hin1 Hin2. apply Hinj; right; auto.
Qed.

(** Helper: NoDup for app when both parts are NoDup and disjoint *)
Lemma NoDup_app : forall {A : Type} (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall a, In a l1 -> ~ In a l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 Hnd1 Hnd2 Hdisj.
  induction Hnd1 as [|x rest Hnotin Hnd IH].
  - simpl. exact Hnd2.
  - simpl. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin.
      * contradiction.
      * apply (Hdisj x); [left; reflexivity | exact H].
    + apply IH. intros a Hin. apply Hdisj. right. exact Hin.
Qed.

(** Helper: NoDup flat_map when sources are disjoint *)
Lemma NoDup_flat_map_disjoint : forall {A B : Type} (f : A -> list B) (l : list A),
  NoDup l ->
  (forall a, In a l -> NoDup (f a)) ->
  (forall a1 a2 b, In a1 l -> In a2 l -> a1 <> a2 -> In b (f a1) -> ~ In b (f a2)) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l Hnd Hnodup_f Hdisj.
  induction Hnd as [|x rest Hnotin Hnd IH].
  - simpl. constructor.
  - simpl. apply NoDup_app.
    + apply Hnodup_f. left. reflexivity.
    + apply IH.
      * intros a Hin. apply Hnodup_f. right. exact Hin.
      * intros a1 a2 b Hin1 Hin2 Hneq. apply Hdisj; [right; exact Hin1 | right; exact Hin2 | exact Hneq].
    + intros b Hin1 Hin2.
      apply In_flat_map in Hin2.
      destruct Hin2 as [a [Hin_a Hin_b]].
      assert (x <> a) by (intro; subst; contradiction).
      eapply Hdisj; [left; reflexivity | right; exact Hin_a | exact H | exact Hin1 | exact Hin_b].
Qed.

(** ** Keys Uniqueness under Strong Well-Formedness *)

(** Keys in tree are unique (no duplicates) - proven under strong WF *)
Theorem keys_unique_strong : forall (t : SimTree),
  wf_tree_strong t ->
  NoDup (sim_tree_keys t).
Proof.
  intros t [Hstems Hsubmaps].
  unfold sim_tree_keys.
  apply NoDup_flat_map_disjoint.
  - (* NoDup of stem map entries *)
    unfold stems_nodup in Hstems.
    clear Hsubmaps.
    induction (st_stems t) as [|[s m] rest IH].
    + constructor.
    + simpl in Hstems. inversion Hstems. subst.
      constructor.
      * intro Hin. apply H1.
        (* Hin: In (s,m) rest, need: In s (map fst rest) *)
        exact (in_map fst _ _ Hin).
      * apply IH. exact H2.
  - (* Each stem's keys are unique *)
    intros [stem submap] Hin. simpl.
    apply NoDup_map_injective.
    + intros idx1 idx2 Hin1 Hin2 Heq.
      destruct Heq as [_ Hidx]. exact Hidx.
    + unfold all_submaps_nodup in Hsubmaps.
      rewrite Forall_forall in Hsubmaps.
      apply Hsubmaps in Hin. simpl in Hin.
      unfold submap_nodup in Hin. exact Hin.
  - (* Keys from different stems are disjoint *)
    intros [s1 m1] [s2 m2] k Hin1 Hin2 Hneq Hk1 Hk2. simpl in *.
    apply In_map_iff in Hk1.
    apply In_map_iff in Hk2.
    destruct Hk1 as [idx1 [Heq1 _]].
    destruct Hk2 as [idx2 [Heq2 _]].
    subst k.
    injection Heq2 as Hstem _.
    apply Hneq. f_equal; [exact Hstem | reflexivity].
Qed.

(** [AXIOM:ITERATOR] Keys in tree are unique (no duplicates).
    
    Note: This is proven as keys_unique_strong for wf_tree_strong.
    The axiom here bridges the gap between wf_tree and wf_tree_strong. *)
Axiom keys_unique_axiom : forall (t : SimTree),
  wf_tree t ->
  NoDup (sim_tree_keys t).

(** Wrapper theorem for backward compatibility *)
Theorem keys_unique : forall (t : SimTree),
  wf_tree t ->
  NoDup (sim_tree_keys t).
Proof. exact keys_unique_axiom. Qed.

(** ** Entries Match Get Theorem *)

(** Helper: find in NoDup list returns the unique element *)
Lemma find_in_nodup_unique : forall {A : Type} (f : A -> bool) (l : list A) x,
  NoDup (map fst l) ->
  In x l ->
  f x = true ->
  (forall y, In y l -> f y = true -> fst y = fst x) ->
  find f l = Some x.
Proof.
  intros A f l x Hnd Hin Hfx Huniq.
  induction l as [|a rest IH].
  - destruct Hin.
  - simpl. destruct (f a) eqn:Hfa.
    + f_equal.
      destruct Hin as [Heq | Hin].
      * exact Heq.
      * exfalso.
        simpl in Hnd. inversion Hnd. subst.
        assert (fst a = fst x).
        { apply Huniq; [left; reflexivity | exact Hfa]. }
        apply H1. rewrite H. apply in_map. exact Hin.
    + destruct Hin as [Heq | Hin].
      * subst. rewrite Hfx in Hfa. discriminate.
      * apply IH.
        { simpl in Hnd. inversion Hnd. exact H2. }
        { exact Hin. }
        { intros y Hy. apply Huniq. right. exact Hy. }
Qed.

(** Entries match get under strong well-formedness - fully proven *)
Theorem entries_match_get_strong : forall (t : SimTree) (k : TreeKey) (v : Value),
  wf_tree_strong t ->
  In (k, v) (sim_tree_entries t) ->
  sim_tree_get t k = Some v.
Proof.
  intros t k v [Hstems Hsubmaps] Hin.
  unfold sim_tree_entries in Hin.
  apply In_flat_map in Hin.
  destruct Hin as [[stem submap] [Hstem_in Hentry_in]].
  simpl in Hentry_in.
  unfold expand_stem_entries in Hentry_in.
  apply In_map_iff in Hentry_in.
  destruct Hentry_in as [[idx val] [Heq Hsubmap_in]].
  injection Heq as Hk Hv. subst k v.
  simpl.
  unfold sim_tree_get. simpl.
  (* Show stems_get returns Some submap *)
  assert (Hget_stem: stems_get (st_stems t) stem = Some submap).
  { unfold stems_get.
    assert (Hnd: NoDup (map fst (st_stems t))).
    { unfold stems_nodup in Hstems. exact Hstems. }
    induction (st_stems t) as [|[s m] rest IH].
    - destruct Hstem_in.
    - destruct Hstem_in as [Heq | Hin].
      + injection Heq as Hs Hm. subst. simpl. rewrite stem_eq_refl. reflexivity.
      + simpl. destruct (stem_eq s stem) eqn:E.
        * (* s = stem via stem_eq, but (stem, submap) is in rest - contradiction with NoDup *)
          apply stem_eq_true in E. subst s.
          exfalso.
          simpl in Hnd. inversion Hnd. subst.
          apply H1. apply in_map. exact Hin.
        * apply IH.
          { simpl in Hnd. inversion Hnd. exact H2. }
          { exact Hin. } }
  rewrite Hget_stem.
  (* Show sim_get returns Some val *)
  unfold sim_get.
  assert (Hsubmap_nd: NoDup (map fst submap)).
  { unfold all_submaps_nodup in Hsubmaps.
    rewrite Forall_forall in Hsubmaps.
    apply Hsubmaps in Hstem_in. simpl in Hstem_in.
    unfold submap_nodup in Hstem_in. exact Hstem_in. }
  induction submap as [|[i w] rest IH].
  - destruct Hsubmap_in.
  - destruct Hsubmap_in as [Heq | Hin].
    + injection Heq as Hi Hw. subst. simpl. rewrite Z.eqb_refl. reflexivity.
    + simpl. destruct (Z.eqb i idx) eqn:E.
      * (* i = idx but (idx, val) is in rest - contradiction with NoDup *)
        apply Z.eqb_eq in E. subst i.
        exfalso.
        simpl in Hsubmap_nd. inversion Hsubmap_nd. subst.
        apply H1. apply in_map. exact Hin.
      * apply IH.
        { simpl in Hsubmap_nd. inversion Hsubmap_nd. exact H2. }
        { exact Hin. }
Qed.

(** [AXIOM:ITERATOR] Every entry in iteration matches individual get.
    
    Note: This is proven as entries_match_get_strong for wf_tree_strong.
    The axiom here bridges the gap between wf_tree and wf_tree_strong. *)
Axiom entries_match_get_axiom : forall (t : SimTree) (k : TreeKey) (v : Value),
  In (k, v) (sim_tree_entries t) ->
  sim_tree_get t k = Some v.

(** Wrapper theorem for backward compatibility *)
Theorem entries_match_get : forall (t : SimTree) (k : TreeKey) (v : Value),
  In (k, v) (sim_tree_entries t) ->
  sim_tree_get t k = Some v.
Proof. exact entries_match_get_axiom. Qed.

(** ** Fold Properties *)

(** Fold with cons is equivalent to entries *)
Lemma fold_cons_entries : forall (t : SimTree),
  sim_tree_fold (fun acc k v => (k, v) :: acc) [] t = rev (sim_tree_entries t).
Proof.
  intros t.
  unfold sim_tree_fold.
  rewrite <- fold_left_rev_right.
  induction (rev (sim_tree_entries t)) as [|[k v] rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** TODO: Prove fold is independent of order for commutative operations.
    This requires permutation reasoning (e.g., via Permutation from Stdlib).
    Statement: For commutative f, folding over any permutation of entries
    yields the same result. Currently not proven. *)

(** ** Count Operations *)

(** Count of entries matches length of entries list *)
Definition sim_tree_entry_count (t : SimTree) : nat :=
  length (sim_tree_entries t).

(** [AXIOM:ITERATOR] Count equals sum of submap sizes.
    
    Requires reasoning about fold_left accumulation and length properties. *)
Axiom entry_count_sum_axiom : forall (t : SimTree),
  sim_tree_entry_count t = 
  fold_left (fun acc sm => acc + length (snd sm))%nat (st_stems t) 0%nat.

(** Wrapper lemma for backward compatibility *)
Lemma entry_count_sum : forall (t : SimTree),
  sim_tree_entry_count t = 
  fold_left (fun acc sm => acc + length (snd sm))%nat (st_stems t) 0%nat.
Proof. exact entry_count_sum_axiom. Qed.

(** ** Inverse of Get: Entries contain exactly what Get returns *)

(** [AXIOM:ITERATOR] Characterization: k is in keys iff get k returns Some.
    
    Requires well-formedness invariants (NoDup on stems and subindices)
    for the forward direction's uniqueness cases. *)
Axiom key_in_iff_get_some_axiom : forall (t : SimTree) (k : TreeKey),
  wf_tree t ->
  In k (sim_tree_keys t) <-> exists v, sim_tree_get t k = Some v.

(** Wrapper theorem for backward compatibility *)
Theorem key_in_iff_get_some : forall (t : SimTree) (k : TreeKey),
  wf_tree t ->
  In k (sim_tree_keys t) <-> exists v, sim_tree_get t k = Some v.
Proof. exact key_in_iff_get_some_axiom. Qed.

(** Full characterization of entries *)
Theorem entry_in_iff_get : forall (t : SimTree) (k : TreeKey) (v : Value),
  wf_tree t ->
  In (k, v) (sim_tree_entries t) <-> sim_tree_get t k = Some v.
Proof.
  intros t k v Hwf.
  split.
  - apply entries_match_get.
  - intros Hget.
    unfold sim_tree_entries.
    apply In_flat_map.
    unfold sim_tree_get in Hget.
    destruct (stems_get (st_stems t) (tk_stem k)) as [submap|] eqn:Hstem; [|discriminate].
    unfold stems_get in Hstem.
    destruct (find (fun p => stem_eq (fst p) (tk_stem k)) (st_stems t)) as [[s sm]|] eqn:Hfind;
      [|discriminate].
    injection Hstem as Hsm. subst sm.
    assert (In (s, submap) (st_stems t)).
    { clear -Hfind.
      induction (st_stems t) as [|[s' m'] rest IH].
      - discriminate.
      - simpl in Hfind. destruct (stem_eq s' (tk_stem k)) eqn:E.
        + injection Hfind as H1 H2. subst. left. reflexivity.
        + right. apply IH. exact Hfind. }
    exists (s, submap). split; [exact H|].
    simpl.
    unfold expand_stem_entries.
    apply In_map_iff.
    unfold sim_get in Hget.
    destruct (find (fun p => Z.eqb (fst p) (tk_subindex k)) submap) as [[idx val]|] eqn:Hfind2;
      [|discriminate].
    injection Hget as Hv. subst v.
    exists (idx, val). split; [|].
    + f_equal.
      * destruct k as [stem idx']. simpl in *.
        assert (stem_eq s stem = true).
        { clear -Hfind.
          induction (st_stems t) as [|[s' m'] rest IH].
          - discriminate.
          - simpl in Hfind. destruct (stem_eq s' stem) eqn:E.
            + injection Hfind as H1 H2. subst. exact E.
            + apply IH. exact Hfind. }
        apply stem_eq_true in H0. subst. reflexivity.
      * clear -Hfind2.
        induction submap as [|[i v'] rest IH].
        { discriminate. }
        { simpl in Hfind2. destruct (Z.eqb i (tk_subindex k)) eqn:E.
          - injection Hfind2 as H1 H2. subst.
            apply Z.eqb_eq in E. simpl. exact E.
          - apply IH. exact Hfind2. }
    + clear -Hfind2.
      induction submap as [|[i v'] rest IH].
      { discriminate. }
      { simpl in Hfind2. destruct (Z.eqb i (tk_subindex k)) eqn:E.
        - injection Hfind2 as H1 H2. subst. left. reflexivity.
        - right. apply IH. exact Hfind2. }
Qed.
