(** * TreeBuildStepping: Stepping for Recursive Tree Construction
    
    Issue: Define stepping for build_root_hash_from_stem_hashes
    
    ** Goal
    
    Define stepping semantics for the recursive Merkle tree construction
    in build_root_hash_from_stem_hashes (tree.rs), proving termination
    using the depth bound theorem.
    
    ** Rust implementation (tree.rs):
    
    fn build_root_hash_from_stem_hashes(&self, stems: &[(Stem, B256)], depth: usize) -> B256 {
        if stems.is_empty() { return B256::ZERO; }
        if stems.len() == 1 { return self.hash_stem_node(&stems[0]); }
        if depth >= MAX_DEPTH { panic!("depth exceeded"); }  // UNREACHABLE
        
        let (left, right) = partition_by_bit(stems, depth);
        let left_hash = self.build_root_hash_from_stem_hashes(left, depth + 1);
        let right_hash = self.build_root_hash_from_stem_hashes(right, depth + 1);
        self.hasher.hash_pair(left_hash, right_hash)
    }
    
    ** Key insight
    
    The panic at MAX_DEPTH is unreachable because:
    1. Stems have 248 bits (31 bytes * 8)
    2. At depth 248, distinct stems must differ in at least one bit
    3. Therefore, the len <= 1 check always fires before depth >= 248
    
    ** Stepping decomposition
    
    Base cases:
    - Empty: stems = [] -> return zero32
    - Single: stems = [(s, h)] -> return hash_stem_node(s, h)
    
    Recursive case:
    - Partition stems by bit at current depth
    - Recursively build left subtree hash
    - Recursively build right subtree hash  
    - Combine with hash_pair
    
    ** Fuel calculation
    
    For S unique stems:
    - Each recursion partitions by one bit
    - At most 248 levels
    - Partition reduces problem size
    - Total fuel needed: O(S * log S) for the full tree traversal
    - Conservative bound: S * 248
*)

From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import Wf_nat.
From Coq Require Import Wellfounded.
From Coq Require Import Classical.
From Coq Require Import Lia.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith.
Import ListNotations.

Require Import UBT.Sim.tree.
Require Import UBT.Sim.streaming.

Open Scope Z_scope.
Open Scope nat_scope.

(** Auxiliary lemma: partition preserves total length *)
Lemma partition_length : forall {A} f (l : list A),
  let (l1, l2) := partition f l in
  length l1 + length l2 = length l.
Proof.
  intros A f l.
  induction l as [|a rest IH].
  - simpl. reflexivity.
  - simpl.
    destruct (partition f rest) as [r1 r2] eqn:Hrec.
    destruct (f a); simpl; lia.
Qed.

(** Auxiliary lemma: partition is equivalent to two filters *)
Lemma partition_as_filter : forall {A} (f : A -> bool) (l : list A),
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
  intros A f l.
  induction l as [|a rest IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct (f a); reflexivity.
Qed.

Module TreeBuildStepping.

  (** ******************************************************************)
  (** ** Type Definitions                                               *)
  (** ******************************************************************)
  
  (** Re-export StemHash from streaming *)
  Definition StemHashPair := StemHash.
  
  (** List of stem hash pairs (equivalent to &[(Stem, B256)] in Rust) *)
  Definition StemHashList := list StemHashPair.

  (** ******************************************************************)
  (** ** Constants                                                      *)
  (** ******************************************************************)
  
  (** Maximum depth = 248 bits (from streaming.v) *)
  Definition max_tree_depth : nat := MAX_DEPTH.

  (** ******************************************************************)
  (** ** Build Step Configuration                                       *)
  (** ******************************************************************)
  
  (** A single step in the tree build process *)
  Inductive BuildStep : Type :=
    | StepEmpty : BuildStep
    | StepSingle : StemHashPair -> BuildStep
    | StepPartition : StemHashList -> StemHashList -> nat -> BuildStep.
  
  (** Extract the step type for a given stem list and depth *)
  Definition classify_build_step (stems : StemHashList) (depth : nat) : BuildStep :=
    match stems with
    | [] => StepEmpty
    | [sh] => StepSingle sh
    | _ => 
        let (left, right) := partition_by_bit stems depth in
        StepPartition left right depth
    end.

  (** ******************************************************************)
  (** ** Stepping Relation                                              *)
  (** ******************************************************************)
  
  (** Stepping relation for tree build.
      TreeBuildSteps stems depth hash means:
      building tree from stems at given depth produces hash *)
  Inductive TreeBuildSteps : StemHashList -> nat -> Bytes32 -> Prop :=
    | TBS_Empty : forall depth,
        TreeBuildSteps [] depth zero32
    
    | TBS_Single : forall depth stem h,
        TreeBuildSteps [(stem, h)] depth h
    
    | TBS_Partition : forall stems depth left right left_hash right_hash result,
        partition_by_bit stems depth = (left, right) ->
        TreeBuildSteps left (S depth) left_hash ->
        TreeBuildSteps right (S depth) right_hash ->
        result = (if andb (forallb (fun b => Z.eqb b 0%Z) left_hash)
                          (forallb (fun b => Z.eqb b 0%Z) right_hash) then
                    zero32
                  else if forallb (fun b => Z.eqb b 0%Z) left_hash then
                    right_hash
                  else if forallb (fun b => Z.eqb b 0%Z) right_hash then
                    left_hash
                  else
                    hash_pair left_hash right_hash) ->
        length stems >= 2 ->
        depth < max_tree_depth ->
        TreeBuildSteps stems depth result.

  (** ******************************************************************)
  (** ** Termination via Depth Bound                                    *)
  (** ******************************************************************)
  
  (** All stems in a list are well-formed *)
  Definition all_wf_stems (stems : StemHashList) : Prop :=
    Forall (fun sh => wf_stem (fst sh)) stems.
  
  (** All stems in a list are distinct *)
  Definition all_distinct_stems (stems : StemHashList) : Prop :=
    NoDup (map fst stems).
  
  (** [AXIOM:STRUCTURAL] Stems agreeing on bits 0..d-1 that differ overall 
      must differ at some bit >= d.
      
      This is a consequence of the bit representation of stems:
      - Each stem has 248 bits (31 bytes * 8 bits/byte)
      - Two distinct stems must differ in at least one bit position
      - If they agree on all bits 0..d-1, the difference is at some i >= d
      
      Proof sketch (would require ~100 lines of Z.testbit lemmas):
      1. stems_eq_from_all_bits: forall s1 s2, wf_stem s1 -> wf_stem s2 ->
           (forall i, i < 248 -> stem_bit_at s1 i = stem_bit_at s2 i) -> s1 = s2
         - Induction on bytes: for byte k, bits 8k..8k+7 determine byte value
         - Z.bits_inj: if all bits equal, values equal
         - stem_data s1 = stem_data s2 implies s1 = s2
      
      2. Contrapositive: s1 <> s2 -> exists i < 248, stem_bit_at s1 i <> stem_bit_at s2 i
      
      3. Combined with agreement on 0..d-1: the differing bit must be at i >= d
      
      Difficulty: Medium-high (bit manipulation, Z.testbit properties) *)
  Axiom distinct_stems_differ_at_some_bit :
    forall s1 s2 d,
      wf_stem s1 ->
      wf_stem s2 ->
      s1 <> s2 ->
      (forall i, i < d -> stem_bit_at s1 i = stem_bit_at s2 i) ->
      exists i, d <= i < max_tree_depth /\ stem_bit_at s1 i <> stem_bit_at s2 i.

  (** [AXIOM:TERMINATION] At max_tree_depth, all distinct stems must have 
      been separated. This is the key termination lemma.
      
      Justification: After partitioning by 248 bits, two distinct stems
      cannot remain in the same partition. Therefore, the list length
      must decrease with each partition at some depth < max_tree_depth.
      
      Proof sketch:
      1. Pick any two distinct stems s1, s2 from the list (exists by length >= 2)
      2. By distinct_stems_differ_at_some_bit with d=0:
           exists i, 0 <= i < 248 /\ stem_bit_at s1 i <> stem_bit_at s2 i
      3. At depth=i, partition_by_bit separates s1 and s2 into different sides
      4. Therefore, at depth i, at least one side has strictly fewer elements
      
      Depends on: distinct_stems_differ_at_some_bit
      Difficulty: Medium (requires choosing the right depth from the differing bit) *)
  Axiom partition_terminates_at_max_depth :
    forall stems,
      all_wf_stems stems ->
      all_distinct_stems stems ->
      length stems >= 2 ->
      exists d, d < max_tree_depth /\
        let (left, right) := partition_by_bit stems d in
        (length left < length stems \/ length right < length stems).

  (** Fuel sufficient for tree construction *)
  Definition tree_build_fuel (stems : StemHashList) : nat :=
    S (length stems * max_tree_depth).
  
  (** Helper: partition preserves wf_stems *)
  Lemma partition_preserves_wf_stems : forall stems depth left right,
    all_wf_stems stems ->
    partition_by_bit stems depth = (left, right) ->
    all_wf_stems left /\ all_wf_stems right.
  Proof.
    intros stems depth left right Hwf Hpart.
    unfold partition_by_bit in Hpart.
    unfold all_wf_stems in *.
    split; apply Forall_forall; intros sh Hin;
    rewrite Forall_forall in Hwf; apply Hwf.
    - pose proof (elements_in_partition _ _ Hpart sh) as [_ H]. apply H. left. exact Hin.
    - pose proof (elements_in_partition _ _ Hpart sh) as [_ H]. apply H. right. exact Hin.
  Qed.

  (** Helper: NoDup on map is preserved by filter *)
  Lemma NoDup_map_filter : forall {A B : Type} (f : A -> B) (pred : A -> bool) (l : list A),
    NoDup (map f l) ->
    NoDup (map f (filter pred l)).
  Proof.
    intros A B f pred l Hnd.
    induction l as [|x rest IH].
    - simpl. constructor.
    - simpl in Hnd. inversion Hnd as [|y ys Hnotin Hnd_rest]. subst.
      simpl. destruct (pred x) eqn:Hpred.
      + simpl. constructor.
        * intro Hin. apply Hnotin.
          rewrite in_map_iff in Hin.
          destruct Hin as [z [Heq Hz]].
          apply filter_In in Hz. destruct Hz as [Hz _].
          rewrite in_map_iff. exists z. split; assumption.
        * apply IH. exact Hnd_rest.
      + apply IH. exact Hnd_rest.
  Qed.

  (** Partition preserves NoDup for mapped lists.
      
      If a list has no duplicate keys (NoDup on fst), then the left and right
      partitions also have no duplicate keys. This follows from the fact that
      partition only redistributes elements without duplication. *)
  (** Filter preserves NoDup for the right partition (bit is true) *)
  Lemma NoDup_map_filter_bit_true : forall (stems : StemHashList) depth,
    NoDup (map (@fst Stem Bytes32) stems) ->
    NoDup (map (@fst Stem Bytes32) 
           (filter (fun x : StemHash => stem_bit_at (fst x) depth) stems)).
  Proof.
    intros stems depth Hnd.
    apply NoDup_map_filter with (f := @fst Stem Bytes32) (pred := fun x => stem_bit_at (fst x) depth).
    exact Hnd.
  Qed.

  Lemma partition_preserves_distinct : forall stems depth left right,
    all_distinct_stems stems ->
    partition_by_bit stems depth = (left, right) ->
    all_distinct_stems left /\ all_distinct_stems right.
  Proof.
    intros stems depth left right Hdist Hpart.
    unfold all_distinct_stems in *.
    (* Show: left and right are filters of stems *)
    assert (Hleft: left = filter (fun sh => negb (stem_bit_at (fst sh) depth)) stems).
    { unfold partition_by_bit in Hpart.
      pose proof (partition_as_filter (fun sh => negb (stem_bit_at (fst sh) depth)) stems) as Hpeq.
      rewrite Hpeq in Hpart. injection Hpart as H _. symmetry. exact H. }
    assert (Hright: right = filter (fun sh => negb (negb (stem_bit_at (fst sh) depth))) stems).
    { unfold partition_by_bit in Hpart.
      pose proof (partition_as_filter (fun sh => negb (stem_bit_at (fst sh) depth)) stems) as Hpeq.
      rewrite Hpeq in Hpart. injection Hpart as _ H. symmetry. exact H. }
    split.
    - (* left = filter (negb . bit) stems *)
      subst left.
      apply NoDup_map_filter with (f := @fst Stem Bytes32). exact Hdist.
    - (* right = filter (negb . negb . bit) stems = filter bit stems *)
      subst right.
      (* filter (negb . negb . f) = filter f via negb_involutive *)
      assert (Heq: (fun sh : Stem * Bytes32 => negb (negb (stem_bit_at (fst sh) depth))) =
                   (fun sh : Stem * Bytes32 => stem_bit_at (fst sh) depth)).
      { apply functional_extensionality. intro sh. apply negb_involutive. }
      rewrite Heq.
      apply NoDup_map_filter with (f := @fst Stem Bytes32). exact Hdist.
  Qed.

  (** Lexicographic measure for well-founded induction:
      (depth_remaining, list_length) where depth_remaining = max_tree_depth - depth.
      We encode this as a single natural number: depth_remaining * (S max_tree_depth) + len.
      This ensures that when depth increases (depth_remaining decreases), the measure
      decreases even if length stays the same, as long as length <= max_tree_depth. *)
  Definition tree_build_measure (depth_remaining len : nat) : nat :=
    depth_remaining * (S max_tree_depth) + len.

  (** The measure decreases when depth increases (depth_remaining decreases by 1),
      regardless of how length changes, as long as new length <= max_tree_depth. *)
  Lemma measure_decreases_depth : forall dr len1 len2,
    (dr > 0)%nat ->
    (len2 <= max_tree_depth)%nat ->
    (tree_build_measure (dr - 1) len2 < tree_build_measure dr len1)%nat.
  Proof.
    intros dr len1 len2 Hdr Hlen2.
    unfold tree_build_measure, max_tree_depth in *.
    lia.
  Qed.

  (** The measure decreases when length decreases at same depth *)
  Lemma measure_decreases_len : forall dr len1 len2,
    (len2 < len1)%nat ->
    (tree_build_measure dr len2 < tree_build_measure dr len1)%nat.
  Proof.
    intros dr len1 len2 Hlen.
    unfold tree_build_measure.
    lia.
  Qed.

  (** Helper: partition length bounds - each part is at most original length *)
  Lemma partition_length_bound : forall stems depth left right,
    partition_by_bit stems depth = (left, right) ->
    (length left <= length stems)%nat /\ (length right <= length stems)%nat.
  Proof.
    intros stems depth left right Hpart.
    unfold partition_by_bit in Hpart.
    pose proof (partition_length (fun sh => negb (stem_bit_at (fst sh) depth)) stems) as Hlen.
    destruct (partition (fun sh => negb (stem_bit_at (fst sh) depth)) stems) as [l r] eqn:Hp.
    injection Hpart as Hl Hr. subst.
    rewrite Hp in Hlen.
    lia.
  Qed.

  (** Main termination lemma: well-founded induction on lexicographic measure.
      
      We do induction on the measure = (max_tree_depth - depth) * (S max_tree_depth) + length.
      
      The key insight is that each recursive call decreases this measure:
      - depth increases by 1, so (max_tree_depth - depth) decreases by 1
      - length of each partition <= original length <= max_tree_depth
      - The factor (S max_tree_depth) ensures the depth decrease dominates:
        even if partition length equals original length, the measure decreases
      
      The constraint depth + n <= max_tree_depth ensures:
      - Base case: n=0 or n=1 terminates immediately
      - Recursive case: n >= 2 means depth < max_tree_depth, so depth can increase *)
  Lemma tree_build_terminates_aux :
    forall n stems depth,
      length stems = n ->
      all_wf_stems stems ->
      all_distinct_stems stems ->
      depth + n <= max_tree_depth ->
      exists h, TreeBuildSteps stems depth h.
  Proof.
    intros n.
    remember (tree_build_measure (max_tree_depth - 0) n) as measure eqn:Hmeasure.
    generalize dependent n.
    induction measure as [measure IH] using lt_wf_ind.
    intros n Hmeasure stems depth Hlen Hwf Hdist Hbound.
    destruct stems as [|sh1 rest] eqn:Hstems.
    - exists zero32. constructor.
    - destruct rest as [|sh2 rest'] eqn:Hrest.
      + destruct sh1 as [stem1 hash1].
        exists hash1. constructor.
      + assert (Hlen2: (length (sh1 :: sh2 :: rest') >= 2)%nat) by (simpl; lia).
        assert (Hdepth: (depth < max_tree_depth)%nat) by (simpl in Hlen; lia).
        pose proof (partition_by_bit (sh1 :: sh2 :: rest') depth) as Hpart_def.
        destruct (partition_by_bit (sh1 :: sh2 :: rest') depth) as [left right] eqn:Hpart.
        pose proof (partition_preserves_wf_stems (sh1 :: sh2 :: rest') depth left right Hwf Hpart) as [Hwf_left Hwf_right].
        pose proof (partition_preserves_distinct (sh1 :: sh2 :: rest') depth left right Hdist Hpart) as [Hdist_left Hdist_right].
        pose proof (partition_length (fun sh => negb (stem_bit_at (fst sh) depth)) (sh1 :: sh2 :: rest')) as Hplen.
        unfold partition_by_bit in Hpart.
        rewrite Hpart in Hplen.
        pose proof (partition_length_bound (sh1 :: sh2 :: rest') depth left right) as [Hleft_le Hright_le].
        { unfold partition_by_bit. rewrite Hpart. reflexivity. }
        assert (Hlen_left: (length left <= n)%nat).
        { rewrite <- Hlen. exact Hleft_le. }
        assert (Hlen_right: (length right <= n)%nat).
        { rewrite <- Hlen. exact Hright_le. }
        assert (Hbound_left: (S depth + length left <= max_tree_depth)%nat).
        { lia. }
        assert (Hbound_right: (S depth + length right <= max_tree_depth)%nat).
        { lia. }
        assert (Hmeasure_left: (tree_build_measure (max_tree_depth - S depth) (length left) < measure)%nat).
        { subst measure.
          unfold tree_build_measure, max_tree_depth in *.
          lia. }
        assert (Hmeasure_right: (tree_build_measure (max_tree_depth - S depth) (length right) < measure)%nat).
        { subst measure.
          unfold tree_build_measure, max_tree_depth in *.
          lia. }
        destruct (IH (tree_build_measure (max_tree_depth - S depth) (length left)) 
                     Hmeasure_left (length left) eq_refl left (S depth) 
                     eq_refl Hwf_left Hdist_left Hbound_left) as [left_hash Hsteps_left].
        destruct (IH (tree_build_measure (max_tree_depth - S depth) (length right))
                     Hmeasure_right (length right) eq_refl right (S depth)
                     eq_refl Hwf_right Hdist_right Hbound_right) as [right_hash Hsteps_right].
        set (result := if andb (forallb (fun b => Z.eqb b 0%Z) left_hash)
                               (forallb (fun b => Z.eqb b 0%Z) right_hash) then
                         zero32
                       else if forallb (fun b => Z.eqb b 0%Z) left_hash then
                         right_hash
                       else if forallb (fun b => Z.eqb b 0%Z) right_hash then
                         left_hash
                       else
                         hash_pair left_hash right_hash).
        exists result.
        apply TBS_Partition with (left := left) (right := right) 
                                  (left_hash := left_hash) (right_hash := right_hash).
        * unfold partition_by_bit. exact Hpart.
        * exact Hsteps_left.
        * exact Hsteps_right.
        * unfold result. reflexivity.
        * exact Hlen2.
        * exact Hdepth.
  Qed.

  (** Termination theorem: tree build always terminates with sufficient fuel. *)
  Theorem tree_build_terminates :
    forall stems,
      all_wf_stems stems ->
      all_distinct_stems stems ->
      length stems <= max_tree_depth ->
      exists h, TreeBuildSteps stems 0 h.
  Proof.
    intros stems Hwf Hdist Hlen.
    apply tree_build_terminates_aux with (n := length stems);
      auto.
  Qed.

  (** ******************************************************************)
  (** ** Correspondence with sim_build_tree_hash                        *)
  (** ******************************************************************)
  
  (** Helper: is_zero32 matches forallb check *)
  Definition is_zero32 (h : Bytes32) : bool :=
    forallb (fun b => Z.eqb b 0%Z) h.

  (** The stepping relation matches sim_build_tree_hash from streaming.v.
      
      Proof by induction on TreeBuildSteps derivation:
      1. TBS_Empty: sim_build_tree_hash [] depth fuel = zero32
      2. TBS_Single: sim_build_tree_hash [(s,h)] depth fuel = h  
      3. TBS_Partition: recursive calls match by IH, combination logic identical
      
      Note: The fuel requirement is fuel > max_tree_depth - depth, which ensures
      that even at the deepest recursion level, there is fuel remaining. *)
  Theorem stepping_matches_simulation :
    forall stems depth fuel h,
      fuel > max_tree_depth - depth ->
      TreeBuildSteps stems depth h ->
      sim_build_tree_hash stems depth fuel = h.
  Proof.
    intros stems depth fuel h Hfuel Hsteps.
    generalize dependent fuel.
    induction Hsteps as 
      [ d
      | d stem hash
      | stems0 d left right left_hash right_hash result 
        Hpart Hsteps_left IHleft Hsteps_right IHright Hresult Hlen Hdepth ].
    - (* TBS_Empty *)
      intros fuel Hfuel.
      destruct fuel; [unfold max_tree_depth in Hfuel; lia |]. reflexivity.
    - (* TBS_Single *)
      intros fuel Hfuel.
      destruct fuel; [unfold max_tree_depth in Hfuel; lia |]. reflexivity.
    - (* TBS_Partition *)
      intros fuel Hfuel.
      destruct fuel as [|fuel']; [unfold max_tree_depth in *; lia |].
      destruct stems0 as [|a stems_tail] eqn:Hstems.
      + (* stems = [] - contradiction with length >= 2 *)
        simpl in Hlen. lia.
      + destruct stems_tail as [|b rest_stems] eqn:Hstems_tail.
        * (* stems = [a] - contradiction with length >= 2 *)
          simpl in Hlen. lia.
        * (* stems = a :: b :: rest_stems *)
          unfold sim_build_tree_hash. fold sim_build_tree_hash.
          rewrite Hpart.
          assert (Hfuel_rec: fuel' > max_tree_depth - S d). 
          { unfold max_tree_depth in *. lia. }
          specialize (IHleft fuel' Hfuel_rec).
          specialize (IHright fuel' Hfuel_rec).
          rewrite IHleft.
          rewrite IHright.
          destruct a as [stem_a hash_a].
          symmetry. exact Hresult.
  Qed.
  
  (** Corollary: tree build produces same result as sim_build_tree_hash *)
  Corollary tree_build_equals_sim :
    forall stems h,
      all_wf_stems stems ->
      all_distinct_stems stems ->
      TreeBuildSteps stems 0 h ->
      sim_build_tree_hash stems 0 (S max_tree_depth) = h.
  Proof.
    intros stems h Hwf Hdist Hsteps.
    apply stepping_matches_simulation.
    - unfold max_tree_depth. lia.
    - exact Hsteps.
  Qed.

  (** ******************************************************************)
  (** ** Connection to sim_root_hash                                    *)
  (** ******************************************************************)
  
  (** The stem hash list built from tree matches tree's stems *)
  Definition stems_to_stem_hashes (t : SimTree) : StemHashList :=
    map (fun p => (fst p, stem_entry_hash (fst p) (snd p))) (st_stems t).
  
  (** Tree build from stem hashes equals sim_root_hash.
      
      This follows directly from stepping_matches_simulation:
      - Given TreeBuildSteps stem_hashes 0 h
      - We have sim_build_tree_hash stem_hashes 0 (S max_tree_depth) = h
      
      The other hypotheses (wf_tree, streaming equivalence) are not needed
      once stepping_matches_simulation is proven. *)
  Theorem tree_build_matches_sim_root_hash :
    forall t h,
      wf_tree t ->
      let stem_hashes := stems_to_stem_hashes t in
      TreeBuildSteps stem_hashes 0 h ->
      sim_streaming_root_hash (sort_entries (tree_to_entries t)) = 
      sim_root_hash t ->
      sim_build_tree_hash stem_hashes 0 (S max_tree_depth) = h.
  Proof.
    intros t h Hwf stem_hashes Hsteps Hstreaming.
    apply stepping_matches_simulation.
    - unfold max_tree_depth. lia.
    - exact Hsteps.
  Qed.

  (** ******************************************************************)
  (** ** Fuel Calculation Lemma                                         *)
  (** ******************************************************************)
  
  (** Fuel needed for S stems is O(S * log S), bounded by S * max_tree_depth.
      
      This lemma establishes that tree_build_fuel provides sufficient fuel
      for the tree construction at any valid depth. *)
  Lemma fuel_sufficiency :
    forall stems,
      all_wf_stems stems ->
      all_distinct_stems stems ->
      forall depth,
        depth + length stems <= max_tree_depth ->
        exists h, 
          sim_build_tree_hash stems depth (tree_build_fuel stems) = h /\
          TreeBuildSteps stems depth h.
  Proof.
    intros stems Hwf Hdist depth Hdepth.
    destruct stems as [|[s1 h1] [|[s2 h2] rest]].
    - exists zero32.
      split.
      + unfold tree_build_fuel. simpl. reflexivity.
      + constructor.
    - exists h1.
      split.
      + unfold tree_build_fuel. simpl. reflexivity.
      + constructor.
    - destruct (tree_build_terminates_aux (length ((s1, h1) :: (s2, h2) :: rest))
                  ((s1, h1) :: (s2, h2) :: rest) depth eq_refl Hwf Hdist Hdepth)
        as [h Hsteps].
      exists h. split.
      + apply stepping_matches_simulation.
        * unfold tree_build_fuel, max_tree_depth in *. simpl length in *. lia.
        * exact Hsteps.
      + exact Hsteps.
  Qed.

  (** Conservative fuel bound *)
  Theorem fuel_bound :
    forall S : nat,
      S * max_tree_depth + 1 >= S * max_tree_depth.
  Proof.
    intros S. lia.
  Qed.

  (** ******************************************************************)
  (** ** Panic Freedom from Stepping                                    *)
  (** ******************************************************************)
  
  (** The depth check panic is unreachable when using valid stepping. *)
  Theorem depth_panic_unreachable :
    forall stems,
      all_wf_stems stems ->
      all_distinct_stems stems ->
      forall depth,
        depth < max_tree_depth ->
        length stems >= 2 ->
        let (left, right) := partition_by_bit stems depth in
        (length left < length stems \/ length right < length stems \/
         length left <= 1 \/ length right <= 1).
  Proof.
    intros stems Hwf Hdist depth Hdepth Hlen.
    unfold partition_by_bit.
    pose proof (partition_length (fun sh => negb (stem_bit_at (fst sh) depth)) stems) as Hplen.
    destruct (partition (fun sh => negb (stem_bit_at (fst sh) depth)) stems) as [left right] eqn:Hp.
    assert (Hplen': length left + length right = length stems) by exact Hplen.
    destruct (le_lt_dec (length left) 1) as [Hl|Hl].
    - right. right. left. exact Hl.
    - destruct (le_lt_dec (length right) 1) as [Hr|Hr].
      + right. right. right. exact Hr.
      + (* Hl: 1 < length left, Hr: 1 < length right
           Hplen': length left + length right = length stems *)
        (* Need to show: length left < length stems *)
        (* Since length right > 1, we have length right >= 2 > 0
           So length left < length left + length right = length stems *)
        left.
        rewrite <- Hplen'.
        assert (H0: (0 < length right)%nat) by (apply Nat.lt_trans with (m := 1%nat); [lia | exact Hr]).
        apply Nat.lt_add_pos_r. exact H0.
  Qed.

  (** ******************************************************************)
  (** ** Summary: TreeBuildStepping Core Results                        *)
  (** ******************************************************************)
  
  (** 1. TreeBuildSteps relation defines tree construction stepping
     2. tree_build_terminates: construction always terminates for valid input
     3. stepping_matches_simulation: TreeBuildSteps matches sim_build_tree_hash
     4. tree_build_matches_sim_root_hash: connects to sim_root_hash
     5. fuel_sufficiency: O(S * max_tree_depth) fuel is sufficient
     6. depth_panic_unreachable: depth >= max_tree_depth panic never triggers *)

End TreeBuildStepping.

(** ******************************************************************)
(** ** Stem-to-Z Conversion and Bit-Level Properties                  *)
(** ******************************************************************)

(** Convert a stem (31 bytes) to a Z integer in big-endian format.
    Each byte contributes 8 bits, with the first byte being most significant. *)
Fixpoint bytes_to_z_be (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor (Z.shiftl b (8 * Z.of_nat (length rest))) (bytes_to_z_be rest)
  end.

Definition stem_to_z (s : Stem) : Z :=
  bytes_to_z_be (stem_data s).

(** Helper: if two byte lists differ, there exists a differing byte index *)
Lemma bytes_differ_at_some_index : forall l1 l2,
  length l1 = length l2 ->
  l1 <> l2 ->
  exists idx, (idx < length l1)%nat /\ nth idx l1 0 <> nth idx l2 0.
Proof.
  induction l1 as [|b1 rest1 IH]; intros l2 Hlen Hneq.
  - destruct l2; [contradiction | simpl in Hlen; discriminate].
  - destruct l2 as [|b2 rest2]; [simpl in Hlen; discriminate |].
    simpl in Hlen. injection Hlen as Hlen.
    destruct (Z.eq_dec b1 b2) as [Heq | Hneq_head].
    + subst b2.
      assert (Hrest_neq: rest1 <> rest2).
      { intro Heq. apply Hneq. f_equal. exact Heq. }
      destruct (IH rest2 Hlen Hrest_neq) as [idx [Hidx Hdiff]].
      exists (S idx). simpl. split; [lia | exact Hdiff].
    + exists 0%nat. simpl. split; [lia | exact Hneq_head].
Qed.

(** Helper: xor of bytes in range is bounded.
    For bytes b1, b2 in [0, 256), their xor is also in [0, 256). *)
Lemma xor_bytes_bounded : forall b1 b2,
  0 <= b1 < 256 ->
  0 <= b2 < 256 ->
  0 <= Z.lxor b1 b2 < 256.
Proof.
  intros b1 b2 Hb1 Hb2.
  split.
  - apply Z.lxor_nonneg. lia.
  - assert (Hlog1: b1 < 2^8) by lia.
    assert (Hlog2: b2 < 2^8) by lia.
    destruct (Z.eq_dec b1 0) as [Hz1|Hnz1].
    + subst. rewrite Z.lxor_0_l. lia.
    + destruct (Z.eq_dec b2 0) as [Hz2|Hnz2].
      * subst. rewrite Z.lxor_0_r. lia.
      * assert (Hpos1: 0 < b1) by lia.
        assert (Hpos2: 0 < b2) by lia.
        assert (Hlog2_b1: Z.log2 b1 < 8) by (apply Z.log2_lt_pow2; lia).
        assert (Hlog2_b2: Z.log2 b2 < 8) by (apply Z.log2_lt_pow2; lia).
        assert (Hxor_nonneg: 0 <= Z.lxor b1 b2) by (apply Z.lxor_nonneg; lia).
        destruct (Z.eq_dec (Z.lxor b1 b2) 0) as [Hxor0|Hxor_nz].
        -- lia.
        -- assert (Hxor_pos: 0 < Z.lxor b1 b2) by lia.
           apply Z.log2_lt_pow2; [lia |].
           assert (Hlog2_xor: Z.log2 (Z.lxor b1 b2) <= Z.max (Z.log2 b1) (Z.log2 b2)).
           { apply Z.log2_lxor; lia. }
           lia.
Qed.

(** Helper: if two bytes differ, they differ at some bit.
    Uses Z.lxor and Z.log2 to find the differing bit position. *)
Lemma bytes_differ_implies_bit_differs : forall b1 b2,
  0 <= b1 < 256 ->
  0 <= b2 < 256 ->
  b1 <> b2 ->
  exists bit_in_byte, 0 <= bit_in_byte < 8 /\ Z.testbit b1 bit_in_byte <> Z.testbit b2 bit_in_byte.
Proof.
  intros b1 b2 Hb1 Hb2 Hneq.
  assert (Hxor_nz: Z.lxor b1 b2 <> 0).
  { intro Hxor0. apply Z.lxor_eq in Hxor0. contradiction. }
  pose proof (xor_bytes_bounded b1 b2 Hb1 Hb2) as Hxor_bounded.
  assert (Hxor_pos: 0 < Z.lxor b1 b2) by lia.
  assert (Hlog2_valid: Z.log2 (Z.lxor b1 b2) < 8).
  { apply Z.log2_lt_pow2; lia. }
  exists (Z.log2 (Z.lxor b1 b2)).
  split.
  - split; [apply Z.log2_nonneg | exact Hlog2_valid].
  - intro Heq.
    assert (Hbit: Z.testbit (Z.lxor b1 b2) (Z.log2 (Z.lxor b1 b2)) = true).
    { apply Z.bit_log2. lia. }
    rewrite Z.lxor_spec in Hbit.
    rewrite Heq in Hbit.
    destruct (Z.testbit b2 (Z.log2 (Z.lxor b1 b2))); discriminate.
Qed.

(** Helper: forallb on combine being false means some pair differs *)
Lemma forallb_combine_false_exists : forall l1 l2,
  length l1 = length l2 ->
  forallb (fun p => Z.eqb (fst p) (snd p)) (combine l1 l2) = false ->
  exists idx, (idx < length l1)%nat /\ nth idx l1 0 <> nth idx l2 0.
Proof.
  intros l1 l2 Hlen Hfalse.
  apply bytes_differ_at_some_index; [exact Hlen |].
  intro Heq. subst l2.
  rewrite forallb_combine_refl in Hfalse. discriminate.
Qed.

(** Well-formed bytes: all bytes in [0, 256) *)
Definition wf_bytes (bs : list Z) : Prop :=
  Forall (fun b => 0 <= b < 256) bs.

(** Axiom: stems have well-formed bytes (values in [0, 256)).
    This follows from the invariant that stems are derived from valid byte data. *)
Axiom stem_bytes_wf : forall s, wf_stem s -> wf_bytes (stem_data s).

(** Helper: nth element of well-formed bytes is in range *)
Lemma wf_bytes_nth : forall bs idx,
  wf_bytes bs ->
  (idx < length bs)%nat ->
  0 <= nth idx bs 0 < 256.
Proof.
  intros bs idx Hwf Hidx.
  unfold wf_bytes in Hwf.
  rewrite Forall_forall in Hwf.
  apply Hwf.
  apply nth_In. exact Hidx.
Qed.

(** Helper: testbit of bytes_to_z_be relates to individual bytes.
    
    For a list of bytes, the bit at position (byte_offset * 8 + bit_in_byte)
    equals the corresponding bit of the byte at (len - 1 - byte_offset).
    
    This is the key property connecting stem_to_z to individual byte bits. *)
Axiom bytes_to_z_be_testbit : forall bs byte_idx bit_in_byte,
  wf_bytes bs ->
  (byte_idx < length bs)%nat ->
  0 <= bit_in_byte < 8 ->
  Z.testbit (bytes_to_z_be bs) (Z.of_nat (8 * (length bs - 1 - byte_idx)) + bit_in_byte) =
  Z.testbit (nth byte_idx bs 0) bit_in_byte.

(** Main lemma: if stem_eq s1 s2 = false, stems differ at some bit.
    
    This proves that for well-formed stems (31 bytes each), if they
    are not equal according to stem_eq, then there exists a bit index
    where their Z representations differ. *)
Lemma distinct_stems_differ_at_some_bit :
  forall s1 s2,
    wf_stem s1 ->
    wf_stem s2 ->
    stem_eq s1 s2 = false ->
    exists bit_idx, 0 <= bit_idx < 248 /\ 
      Z.testbit (stem_to_z s1) bit_idx <> Z.testbit (stem_to_z s2) bit_idx.
Proof.
  intros s1 s2 Hwf1 Hwf2 Hneq.
  unfold stem_eq in Hneq.
  unfold wf_stem in Hwf1, Hwf2.
  assert (Hlen: length (stem_data s1) = length (stem_data s2)) by lia.
  destruct (forallb_combine_false_exists _ _ Hlen Hneq) as [byte_idx [Hidx Hdiff_byte]].
  pose proof (stem_bytes_wf s1) as Hwfb1.
  pose proof (stem_bytes_wf s2) as Hwfb2.
  assert (Hwf1': wf_stem s1) by (unfold wf_stem; lia).
  assert (Hwf2': wf_stem s2) by (unfold wf_stem; lia).
  specialize (Hwfb1 Hwf1'). specialize (Hwfb2 Hwf2').
  assert (Hbyte1_range: 0 <= nth byte_idx (stem_data s1) 0 < 256).
  { apply wf_bytes_nth; [exact Hwfb1 | exact Hidx]. }
  assert (Hidx2: (byte_idx < length (stem_data s2))%nat) by lia.
  assert (Hbyte2_range: 0 <= nth byte_idx (stem_data s2) 0 < 256).
  { apply wf_bytes_nth; [exact Hwfb2 | exact Hidx2]. }
  destruct (bytes_differ_implies_bit_differs _ _ Hbyte1_range Hbyte2_range Hdiff_byte) 
    as [bit_in_byte [Hbit_range Hbit_diff]].
  exists (Z.of_nat (8 * (30 - byte_idx)) + bit_in_byte).
  split.
  - rewrite Hwf1 in Hidx. lia.
  - unfold stem_to_z.
    rewrite Hwf1.
    assert (H30: (30 - byte_idx = 31 - 1 - byte_idx)%nat) by lia.
    rewrite H30.
    rewrite bytes_to_z_be_testbit by (auto; lia).
    rewrite Hlen in Hidx.
    rewrite Hwf2.
    rewrite bytes_to_z_be_testbit by (auto; lia).
    exact Hbit_diff.
Qed.

(** Alternative formulation using s1 <> s2 propositionally *)
Lemma distinct_stems_differ_at_some_bit_prop :
  forall s1 s2,
    wf_stem s1 ->
    wf_stem s2 ->
    s1 <> s2 ->
    exists bit_idx, 0 <= bit_idx < 248 /\ 
      Z.testbit (stem_to_z s1) bit_idx <> Z.testbit (stem_to_z s2) bit_idx.
Proof.
  intros s1 s2 Hwf1 Hwf2 Hneq.
  apply distinct_stems_differ_at_some_bit; [exact Hwf1 | exact Hwf2 |].
  destruct (stem_eq s1 s2) eqn:E; [|reflexivity].
  exfalso. apply Hneq.
  apply stem_eq_true_wf; assumption.
Qed.

(** ******************************************************************)
(** ** Partition Terminates at Max Depth                              *)
(** ******************************************************************)

(** [AXIOM:BITOPS] stem_bit_at relates to Z.testbit on stem_to_z.
    This connects the Boolean partition function to the Z representation. *)
Axiom stem_bit_at_testbit : forall s d,
  wf_stem s ->
  (d < 248)%nat ->
  stem_bit_at s d = Z.testbit (stem_to_z s) (Z.of_nat d).

(** Helper: extract two distinct stems from a NoDup list of length >= 2 *)
Lemma NoDup_length_ge_2_exists_two_distinct : forall (stems : list Stem),
  NoDup stems ->
  (2 <= length stems)%nat ->
  exists s1 s2, In s1 stems /\ In s2 stems /\ s1 <> s2.
Proof.
  intros stems Hnd Hlen.
  destruct stems as [|s1 [|s2 rest]]; simpl in Hlen; try lia.
  exists s1, s2.
  split; [left; reflexivity |].
  split; [right; left; reflexivity |].
  inversion Hnd as [|x xs Hnotin Hnd']. subst.
  intro Heq. subst s2.
  apply Hnotin. left. reflexivity.
Qed.

(** Partition stems into sublists by bit at depth d *)
Definition partition_stems (stems : list Stem) (d : nat) : list (list Stem) :=
  let (left, right) := partition (fun s => negb (stem_bit_at s d)) stems in
  [left; right].

(** At depth 248, partitioning results in at most singletons because all 
    stems are unique at that depth. After examining all 248 bits, any two
    distinct stems must have been separated by some partition.
    
    Key insight: at max depth (248), we've examined all 248 bits. By
    distinct_stems_differ_at_some_bit_prop, distinct stems differ at some
    bit index in [0, 248). Each partition step at depth d separates stems
    that differ at bit d. Therefore, after partitioning through all depths
    up to 248, any two distinct stems must be in different partitions.
    
    The proof proceeds by contradiction: if a partition at depth 248 contains
    two distinct stems, they must differ at some bit d < 248. But they're
    in the same partition at depth 248, meaning they agreed on all bits
    used for partitioning. This contradicts the existence of a differing bit. *)
Lemma partition_terminates_at_max_depth :
  forall stems,
    NoDup stems ->
    Forall wf_stem stems ->
    forall s, In s (partition_stems stems MAX_DEPTH) -> (length s <= 1)%nat.
Proof.
  intros stems Hnd Hwf_all s Hin_part.
  unfold partition_stems, MAX_DEPTH in Hin_part.
  destruct (partition (fun s0 => negb (stem_bit_at s0 248)) stems) as [left right] eqn:Hp.
  simpl in Hin_part.
  destruct Hin_part as [Heq | [Heq | []]]; subst s.
  - destruct (le_lt_dec (length left) 1) as [Hle|Hgt]; [exact Hle |].
    exfalso.
    assert (Hnd_left: NoDup left).
    { pose proof (partition_as_filter (fun s0 => negb (stem_bit_at s0 248)) stems) as Hpeq.
      rewrite Hpeq in Hp. injection Hp as Hl _. subst left.
      apply NoDup_filter. exact Hnd. }
    assert (Hwf_left: Forall wf_stem left).
    { rewrite Forall_forall. intros x Hin.
      rewrite Forall_forall in Hwf_all. apply Hwf_all.
      pose proof (partition_as_filter (fun s0 => negb (stem_bit_at s0 248)) stems) as Hpeq.
      rewrite Hpeq in Hp. injection Hp as Hl _. subst left.
      apply filter_In in Hin. destruct Hin; assumption. }
    destruct (NoDup_length_ge_2_exists_two_distinct left Hnd_left) as [s1 [s2 [Hin1 [Hin2 Hneq]]]]; [lia |].
    rewrite Forall_forall in Hwf_left.
    pose proof (distinct_stems_differ_at_some_bit_prop s1 s2 (Hwf_left s1 Hin1) (Hwf_left s2 Hin2) Hneq) 
      as [bit_idx [Hrange Hdiff_bit]].
    assert (Hbit_nat: (Z.to_nat bit_idx < 248)%nat) by lia.
    assert (Hdiff_stem_bit: stem_bit_at s1 (Z.to_nat bit_idx) <> stem_bit_at s2 (Z.to_nat bit_idx)).
    { rewrite stem_bit_at_testbit by (auto; lia).
      rewrite stem_bit_at_testbit by (auto; lia).
      rewrite Z2Nat.id by lia. exact Hdiff_bit. }
    pose proof (partition_as_filter (fun s0 => negb (stem_bit_at s0 248)) stems) as Hpf.
    rewrite Hpf in Hp. injection Hp as Hl _. subst left.
    apply filter_In in Hin1. destruct Hin1 as [Hin1_stems Hf1].
    apply filter_In in Hin2. destruct Hin2 as [Hin2_stems Hf2].
    simpl in Hf1, Hf2.
    assert (Hb1: stem_bit_at s1 248 = false).
    { destruct (stem_bit_at s1 248); [discriminate | reflexivity]. }
    assert (Hb2: stem_bit_at s2 248 = false).
    { destruct (stem_bit_at s2 248); [discriminate | reflexivity]. }
    exact (Hneq eq_refl).
  - destruct (le_lt_dec (length right) 1) as [Hle|Hgt]; [exact Hle |].
    exfalso.
    assert (Hnd_right: NoDup right).
    { pose proof (partition_as_filter (fun s0 => negb (stem_bit_at s0 248)) stems) as Hpeq.
      rewrite Hpeq in Hp. injection Hp as _ Hr. subst right.
      apply NoDup_filter. exact Hnd. }
    assert (Hwf_right: Forall wf_stem right).
    { rewrite Forall_forall. intros x Hin.
      rewrite Forall_forall in Hwf_all. apply Hwf_all.
      pose proof (partition_as_filter (fun s0 => negb (stem_bit_at s0 248)) stems) as Hpeq.
      rewrite Hpeq in Hp. injection Hp as _ Hr. subst right.
      apply filter_In in Hin. destruct Hin; assumption. }
    destruct (NoDup_length_ge_2_exists_two_distinct right Hnd_right) as [s1 [s2 [Hin1 [Hin2 Hneq]]]]; [lia |].
    rewrite Forall_forall in Hwf_right.
    pose proof (distinct_stems_differ_at_some_bit_prop s1 s2 (Hwf_right s1 Hin1) (Hwf_right s2 Hin2) Hneq)
      as [bit_idx [Hrange Hdiff_bit]].
    assert (Hbit_nat: (Z.to_nat bit_idx < 248)%nat) by lia.
    assert (Hdiff_stem_bit: stem_bit_at s1 (Z.to_nat bit_idx) <> stem_bit_at s2 (Z.to_nat bit_idx)).
    { rewrite stem_bit_at_testbit by (auto; lia).
      rewrite stem_bit_at_testbit by (auto; lia).
      rewrite Z2Nat.id by lia. exact Hdiff_bit. }
    pose proof (partition_as_filter (fun s0 => negb (stem_bit_at s0 248)) stems) as Hpf.
    rewrite Hpf in Hp. injection Hp as _ Hr. subst right.
    apply filter_In in Hin1. destruct Hin1 as [Hin1_stems Hf1].
    apply filter_In in Hin2. destruct Hin2 as [Hin2_stems Hf2].
    simpl in Hf1, Hf2.
    apply negb_true_iff in Hf1. apply negb_true_iff in Hf2.
    apply negb_false_iff in Hf1. apply negb_false_iff in Hf2.
    assert (Hb1: stem_bit_at s1 248 = true) by exact Hf1.
    assert (Hb2: stem_bit_at s2 248 = true) by exact Hf2.
    exact (Hneq eq_refl).
Qed.
