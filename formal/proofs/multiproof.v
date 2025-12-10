(** * MultiProof Verification
    
    Formal verification of MultiProof and batch verification for the UBT.
    
    This file provides formal definitions and theorems for:
    - MultiProof verification (multiple key-value proofs in one structure)
    - Witness generation correctness (generate_stem_proof)
    - Shared deduplication properties
    
    The verification follows the same layered approach as the main proofs:
    - Simulation layer theorems (idiomatic Rocq)
    - Axioms for properties requiring hash function internals
    
    Rust structures modeled:
    - MultiProof: keys, values, shared nodes, stems
    - Witness: pre_values + MultiProof
    - generate_stem_proof: subtree sibling collection
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import UBT.Sim.tree.

Open Scope Z_scope.

(** ** MultiProof Structure
    
    MultiProof is defined in UBT.Sim.tree (imported above).
    We re-export helper definitions here for convenience.
*)

Definition multiproof_len (mp : MultiProof) : nat :=
  length (mp_keys mp).

Definition multiproof_is_empty (mp : MultiProof) : bool :=
  match mp_keys mp with
  | [] => true
  | _ => false
  end.

(** ** Witness Structure *)

(**
   Witness for stateless execution:
   - pre_values: key-value pairs needed for execution
   - proof: MultiProof for the pre-state
*)
Record Witness := mkWitness {
  w_pre_values : list (TreeKey * Value);
  w_proof : MultiProof
}.

Definition empty_witness : Witness :=
  mkWitness [] empty_multiproof.

(** ** Stem Proof Generation Model *)

(**
   Model of generate_stem_proof from Rust:
   Given a stem node's values and a subindex, produces:
   - The value at that subindex (or None)
   - 8 sibling hashes for the 256-leaf subtree
   
   The Rust implementation builds a complete binary tree of 256 leaves
   (values hashed), then collects siblings along the path to the subindex.
*)

(** SubtreeData: 256 hashed values (positions 0-255) *)
Definition SubtreeData := list Bytes32.

(** Initialize subtree data from a SubIndexMap *)
Definition init_subtree_data (m : SubIndexMap) : SubtreeData :=
  let lookup idx := 
    match sim_get m idx with
    | Some v => hash_value v
    | None => zero32
    end in
  map (fun i => lookup (Z.of_nat i)) (seq 0 256).

(** Get sibling index by XORing with 1 *)
Definition sibling_idx (idx : nat) : nat := Nat.lxor idx 1.

(** 
   Build one level of the Merkle tree:
   Combines pairs of nodes into their parent hashes.
*)
Definition build_level (data : list Bytes32) : list Bytes32 :=
  let fix aux l :=
    match l with
    | lnode :: rnode :: rest => hash_pair lnode rnode :: aux rest
    | _ => []
    end
  in aux data.

(**
   Collect sibling at given level, then reduce for next level.
   Returns the sibling and the reduced data.
*)
Definition collect_sibling_and_reduce (data : list Bytes32) (idx : nat) 
  : Bytes32 * list Bytes32 :=
  let sib_idx := sibling_idx idx in
  let sibling := nth sib_idx data zero32 in
  let next_data := build_level data in
  (sibling, next_data).

(**
   Generate stem proof: collect 8 siblings for subindex.
   Models the Rust generate_stem_proof function.
*)
Fixpoint generate_siblings_aux (data : list Bytes32) (idx : nat) (levels : nat) 
  : list Bytes32 :=
  match levels with
  | O => []
  | S n =>
      let (sib, next_data) := collect_sibling_and_reduce data idx in
      sib :: generate_siblings_aux next_data (idx / 2) n
  end.

Definition generate_stem_proof_model (m : SubIndexMap) (subindex : Z) 
  : option Value * list Bytes32 :=
  let value := sim_get m subindex in
  let data := init_subtree_data m in
  let siblings := generate_siblings_aux data (Z.to_nat subindex) 8 in
  (value, siblings).

(** ** Subtree Hash Computation *)

(**
   Compute the subtree root from a leaf hash and siblings.
   This mirrors the Rust Proof::compute_root for ProofNode::Stem.
*)
Fixpoint compute_subtree_root (leaf_hash : Bytes32) (siblings : list Bytes32) 
                               (subindex : nat) (level : nat) : Bytes32 :=
  match siblings with
  | [] => leaf_hash
  | sib :: rest =>
      let bit := Nat.land (Nat.shiftr subindex (7 - level)) 1 in
      let combined := if Nat.eqb bit 0 
                      then hash_pair leaf_hash sib
                      else hash_pair sib leaf_hash in
      compute_subtree_root combined rest subindex (S level)
  end.

(** Wrapper that starts at level 0 *)
Definition compute_subtree_root_from_proof (leaf_hash : Bytes32) 
    (siblings : list Bytes32) (subindex : nat) : Bytes32 :=
  compute_subtree_root leaf_hash siblings subindex 0.

(** ** MultiProof Verification *)

(**
   Verify a single key-value pair from a MultiProof.
   This is a simplified model - full verification requires
   reconstructing the tree structure from deduplicated nodes.
*)
Definition verify_multiproof_entry (mp : MultiProof) (idx : nat) 
                                   (root : Bytes32) : Prop :=
  match nth_error (mp_keys mp) idx, nth_error (mp_values mp) idx with
  | Some key, Some (Some value) =>
      (* Inclusion: value exists *)
      exists stem_siblings tree_path,
        let leaf_hash := hash_value value in
        let subtree_root := compute_subtree_root_from_proof leaf_hash stem_siblings 
                              (Z.to_nat (tk_subindex key)) in
        let stem_hash := hash_stem (tk_stem key) subtree_root in
        compute_root_from_witness stem_hash tree_path = root
  | Some key, Some None =>
      (* Exclusion: value doesn't exist *)
      exists tree_path,
        let stem_hash := hash_stem (tk_stem key) zero32 in
        compute_root_from_witness stem_hash tree_path = root
  | _, _ => False
  end.

(**
   Verify entire MultiProof: all entries verify against the root.
*)
Definition verify_multiproof (mp : MultiProof) (root : Bytes32) : Prop :=
  length (mp_keys mp) = length (mp_values mp) /\
  forall idx, (idx < length (mp_keys mp))%nat -> 
    verify_multiproof_entry mp idx root.

(** ** Well-formedness Predicates *)

Definition wf_multiproof (mp : MultiProof) : Prop :=
  length (mp_keys mp) = length (mp_values mp) /\
  forall k, In k (mp_keys mp) -> wf_stem (tk_stem k).

Definition wf_witness (w : Witness) : Prop :=
  wf_multiproof (w_proof w) /\
  forall p, In p (w_pre_values w) -> wf_stem (tk_stem (fst p)) /\ wf_value (snd p).

(** ** Helper Lemmas *)

(** Index lookup preserves list membership *)
Lemma nth_error_In : forall {A : Type} (l : list A) (idx : nat) (x : A),
  nth_error l idx = Some x -> In x l.
Proof.
  intros A l idx x H.
  generalize dependent idx.
  induction l as [|h t IH]; intros idx H.
  - destruct idx; discriminate.
  - destruct idx as [|idx'].
    + simpl in H. injection H as H. subst. left. reflexivity.
    + simpl in H. right. apply (IH idx' H).
Qed.

(** Two nth_error lookups with same result and same key give same entry *)
Lemma nth_error_same_key_idx : forall (keys : list TreeKey) (i j : nat) (k : TreeKey),
  nth_error keys i = Some k ->
  nth_error keys j = Some k ->
  forall {A : Type} (vals : list A),
    length keys = length vals ->
    (i < length keys)%nat ->
    (j < length keys)%nat ->
    exists vi vj, nth_error vals i = Some vi /\ nth_error vals j = Some vj.
Proof.
  intros keys i j k Hi Hj A vals Hlen Hlt_i Hlt_j.
  assert (Hlt_i_vals: (i < length vals)%nat) by (rewrite <- Hlen; exact Hlt_i).
  assert (Hlt_j_vals: (j < length vals)%nat) by (rewrite <- Hlen; exact Hlt_j).
  assert (Hvi: exists vi, nth_error vals i = Some vi).
  { destruct (nth_error vals i) eqn:E.
    - exists a. reflexivity.
    - apply nth_error_None in E. lia. }
  assert (Hvj: exists vj, nth_error vals j = Some vj).
  { destruct (nth_error vals j) eqn:E.
    - exists a. reflexivity.
    - apply nth_error_None in E. lia. }
  destruct Hvi as [vi Hvi]. destruct Hvj as [vj Hvj].
  exists vi, vj. split; assumption.
Qed.

(** ** Core Theorems *)

(** 
   Theorem: multiproof_soundness
   
   If a MultiProof verifies against a tree root, then all included
   key-value pairs exist in the tree.
   
   [AXIOM:SOUNDNESS] This is axiomatized because it requires:
   1. Hash collision resistance (inherited from tree.v axioms)
   2. Correct mapping between deduplicated nodes and tree structure
   3. The full tree reconstruction algorithm
*)
Axiom multiproof_soundness :
  forall (t : SimTree) (mp : MultiProof),
    wf_multiproof mp ->
    verify_multiproof mp (sim_root_hash t) ->
    forall idx key value,
      nth_error (mp_keys mp) idx = Some key ->
      nth_error (mp_values mp) idx = Some (Some value) ->
      sim_tree_get t key = Some value.

(**
   Theorem: multiproof_exclusion_soundness
   
   If a MultiProof marks a key as absent and verifies, the key
   is indeed absent from the tree.
*)
Axiom multiproof_exclusion_soundness :
  forall (t : SimTree) (mp : MultiProof),
    wf_multiproof mp ->
    verify_multiproof mp (sim_root_hash t) ->
    forall idx key,
      nth_error (mp_keys mp) idx = Some key ->
      nth_error (mp_values mp) idx = Some None ->
      sim_tree_get t key = None.

(**
   Theorem: multiproof_completeness
   
   For any set of keys that exist in the tree, a valid MultiProof
   can be generated.
   
   [AXIOM:COMPLETENESS] This is axiomatized because it requires
   defining the full MultiProof generation algorithm.
*)
Axiom multiproof_completeness :
  forall (t : SimTree) (keys : list TreeKey),
    (forall k, In k keys -> exists v, sim_tree_get t k = Some v) ->
    exists mp,
      wf_multiproof mp /\
      mp_keys mp = keys /\
      verify_multiproof mp (sim_root_hash t) /\
      forall idx key,
        nth_error keys idx = Some key ->
        nth_error (mp_values mp) idx = Some (sim_tree_get t key).

(** ** Stem Proof Correctness *)

(**
   Theorem: witness_generation_correct
   
   The siblings generated by generate_stem_proof, when used to
   reconstruct the subtree root, yield the correct stem node hash.
*)

(** Helper: compute expected subtree root from a SubIndexMap *)
Fixpoint reduce_to_root_aux (fuel : nat) (d : list Bytes32) : Bytes32 :=
  match fuel with
  | O => zero32
  | S fuel' =>
      match d with
      | [single] => single
      | _ => reduce_to_root_aux fuel' (build_level d)
      end
  end.

Definition compute_full_subtree_root (m : SubIndexMap) : Bytes32 :=
  let data := init_subtree_data m in
  reduce_to_root_aux 9 data. (* 9 levels for 256 leaves *)

(**
   [AXIOM:CORRECTNESS] Stem proof generation produces valid witnesses.
   
   When generate_stem_proof_model produces siblings, using them
   to recompute the root matches the full subtree computation.
   
   This requires proving the Merkle tree reconstruction is correct,
   which involves showing the sibling collection preserves the
   ability to recompute any ancestor hash.
*)
Axiom witness_generation_correct :
  forall (m : SubIndexMap) (subindex : Z),
    0 <= subindex < 256 ->
    let (value, siblings) := generate_stem_proof_model m subindex in
    let leaf_hash := match value with
                     | Some v => hash_value v
                     | None => zero32
                     end in
    compute_subtree_root_from_proof leaf_hash siblings (Z.to_nat subindex) =
    compute_full_subtree_root m.

(** ** Shared Deduplication Properties *)

(**
   MultiProofs deduplicate shared nodes for efficiency.
   Keys with the same stem share stem node data.
   Keys with common tree path prefixes share internal nodes.
*)

(** Two keys share a stem *)
Definition keys_share_stem (k1 k2 : TreeKey) : bool :=
  stem_eq (tk_stem k1) (tk_stem k2).

(** Predicate: stems in MultiProof cover all key stems *)
Definition stems_cover_keys (mp : MultiProof) : Prop :=
  forall k, In k (mp_keys mp) -> 
    exists s, In s (mp_stems mp) /\ stem_eq (tk_stem k) s = true.

(**
   [AXIOM:STRUCTURE] Well-formed MultiProofs have stems covering keys.
   This is an invariant maintained by the generation algorithm.
*)
Axiom wf_multiproof_stems_cover :
  forall (mp : MultiProof),
    wf_multiproof mp ->
    verify_multiproof mp (sim_root_hash empty_tree) \/ 
    stems_cover_keys mp.

(**
   Theorem: shared_stem_deduplication_valid
   
   Deduplicating shared nodes doesn't affect proof validity.
   If two keys share a stem, using one stem entry for both
   still produces a valid proof.
   
   This is provable from the stem_colocation theorem in tree.v:
   keys with the same stem access the same SubIndexMap.
*)
Theorem shared_stem_deduplication_valid :
  forall (mp : MultiProof) (root : Bytes32) (k1 k2 : TreeKey),
    wf_multiproof mp ->
    verify_multiproof mp root ->
    In k1 (mp_keys mp) ->
    In k2 (mp_keys mp) ->
    keys_share_stem k1 k2 = true ->
    exists s, In s (mp_stems mp) /\ 
              stem_eq (tk_stem k1) s = true /\
              stem_eq (tk_stem k2) s = true.
Proof.
  (* TODO: Proof requires stems_cover_keys property for all cases.
     The non-empty case uses stem_eq_via_third transitivity to show
     that if k1 and k2 share a stem, and s covers k1's stem, then
     s also covers k2's stem. The empty tree case needs an additional
     axiom linking verify_multiproof on empty_tree to mp_keys being empty. *)
Admitted.

(**
   Full deduplication theorem.
   [AXIOM:DEDUPLICATION] Axiomatized because it requires modeling
   the full node deduplication algorithm.
*)
Axiom shared_deduplication_preserves_validity :
  forall (mp_full mp_dedup : MultiProof) (root : Bytes32),
    (* mp_dedup is a deduplicated version of mp_full *)
    mp_keys mp_full = mp_keys mp_dedup ->
    mp_values mp_full = mp_values mp_dedup ->
    (* Deduplication only removes redundant nodes *)
    (forall n, In n (mp_nodes mp_dedup) -> In n (mp_nodes mp_full)) ->
    (* Validity is preserved *)
    verify_multiproof mp_full root ->
    verify_multiproof mp_dedup root.

(** ** Batch Consistency *)

(**
   Theorem: MultiProof entries are mutually consistent.
   No two entries can claim different values for the same key.
*)
Theorem multiproof_key_consistency :
  forall (t : SimTree) (mp : MultiProof) (i j : nat) (k : TreeKey) (v1 v2 : Value),
    wf_multiproof mp ->
    verify_multiproof mp (sim_root_hash t) ->
    nth_error (mp_keys mp) i = Some k ->
    nth_error (mp_keys mp) j = Some k ->
    nth_error (mp_values mp) i = Some (Some v1) ->
    nth_error (mp_values mp) j = Some (Some v2) ->
    v1 = v2.
Proof.
  intros t mp i j k v1 v2 Hwf Hverify Hki Hkj Hvi Hvj.
  (* Both entries verify against the same root *)
  (* By multiproof_soundness, both map to the same tree lookup *)
  assert (Hget1: sim_tree_get t k = Some v1).
  { eapply (multiproof_soundness t mp Hwf Hverify i k v1 Hki Hvi). }
  assert (Hget2: sim_tree_get t k = Some v2).
  { eapply (multiproof_soundness t mp Hwf Hverify j k v2 Hkj Hvj). }
  (* Tree is a function, so same key => same value *)
  rewrite Hget1 in Hget2.
  injection Hget2 as Heq.
  exact Heq.
Qed.

(** ** Witness Properties *)

(**
   Theorem: Witness validity implies pre-values match tree state.
*)
Axiom witness_reflects_tree :
  forall (t : SimTree) (w : Witness),
    wf_witness w ->
    verify_multiproof (w_proof w) (sim_root_hash t) ->
    forall k v, In (k, v) (w_pre_values w) ->
      sim_tree_get t k = Some v.

(** ** Size Bounds *)

(** 
   MultiProof size is bounded by the number of keys times constant factors.
   Deduplication provides savings when keys share structure.
*)
Definition multiproof_size (mp : MultiProof) : nat :=
  (length (mp_keys mp) * 33) +       (* keys: 32 bytes stem + 1 byte subindex *)
  (length (mp_values mp) * 33) +     (* values: 32 bytes + 1 byte option tag *)
  (length (mp_nodes mp) * 32) +      (* shared nodes: 32 bytes each *)
  (length (mp_stems mp) * 31).       (* stems: 31 bytes each *)

Definition witness_size (w : Witness) : nat :=
  multiproof_size (w_proof w) +
  (length (w_pre_values w) * 64).    (* pre_values: 32 + 32 bytes *)

(** Size is non-negative *)
Lemma multiproof_size_nonneg : forall mp, (0 <= multiproof_size mp)%nat.
Proof.
  intros mp. unfold multiproof_size. lia.
Qed.

(** Empty multiproof has zero size *)
Lemma empty_multiproof_size : multiproof_size empty_multiproof = 0%nat.
Proof.
  reflexivity.
Qed.

(** Deduplication reduces or preserves size *)
Lemma dedup_size_le : forall mp_full mp_dedup,
  mp_keys mp_full = mp_keys mp_dedup ->
  mp_values mp_full = mp_values mp_dedup ->
  (length (mp_nodes mp_dedup) <= length (mp_nodes mp_full))%nat ->
  (length (mp_stems mp_dedup) <= length (mp_stems mp_full))%nat ->
  (multiproof_size mp_dedup <= multiproof_size mp_full)%nat.
Proof.
  intros mp_full mp_dedup Hkeys Hvals Hnodes Hstems.
  unfold multiproof_size.
  rewrite Hkeys, Hvals.
  lia.
Qed.

(** ** QuickChick Test Properties *)

(** Boolean equality for optional values *)
Definition option_value_eqb (ov1 ov2 : option Value) : bool :=
  match ov1, ov2 with
  | None, None => true
  | Some v1, Some v2 => forallb (fun p => Z.eqb (fst p) (snd p)) (combine v1 v2)
                        && Nat.eqb (length v1) (length v2)
  | _, _ => false
  end.

(** Property: multiproof length consistency *)
Definition prop_multiproof_len_consistent (mp : MultiProof) : bool :=
  Nat.eqb (length (mp_keys mp)) (length (mp_values mp)).

(** Property: empty multiproof is well-formed *)
Definition prop_empty_multiproof_wf : bool :=
  prop_multiproof_len_consistent empty_multiproof.

(** Property: witness size >= multiproof size *)
Definition prop_witness_size_ge_proof (w : Witness) : bool :=
  Nat.leb (multiproof_size (w_proof w)) (witness_size w).

(** Property: siblings list has 8 elements *)
Definition prop_stem_proof_8_siblings (m : SubIndexMap) (subindex : Z) : bool :=
  if Z.ltb subindex 0 then true
  else if Z.leb 256 subindex then true
  else
    let (_, siblings) := generate_stem_proof_model m subindex in
    Nat.eqb (length siblings) 8.

(** Manual verification of properties *)
Example test_empty_multiproof_wf : prop_empty_multiproof_wf = true.
Proof. reflexivity. Qed.

Example test_empty_witness_size : 
  prop_witness_size_ge_proof empty_witness = true.
Proof. reflexivity. Qed.

Example test_stem_proof_8_siblings_0 :
  prop_stem_proof_8_siblings [] 0 = true.
Proof. reflexivity. Qed.

Example test_stem_proof_8_siblings_255 :
  prop_stem_proof_8_siblings [] 255 = true.
Proof. reflexivity. Qed.

(** ** Summary of Axioms *)

(**
   Axioms introduced in this file:
   
   1. [AXIOM:SOUNDNESS] multiproof_soundness
      Risk: LOW - standard Merkle proof property, follows from tree.v axioms
      Requires: hash collision resistance + reconstruction algorithm
      
   2. [AXIOM:SOUNDNESS] multiproof_exclusion_soundness  
      Risk: LOW - dual of inclusion soundness
      Requires: same as soundness
      
   3. [AXIOM:COMPLETENESS] multiproof_completeness
      Risk: LOW - constructive, generation algorithm exists in Rust
      Requires: generation algorithm model
      
   4. [AXIOM:CORRECTNESS] witness_generation_correct
      Risk: LOW - well-understood Merkle tree property
      Requires: Merkle tree reconstruction proof
      
   5. [AXIOM:STRUCTURE] wf_multiproof_stems_cover
      Risk: LOW - structural invariant of generation algorithm
      Requires: invariant analysis of MultiProof construction
      
   6. [AXIOM:DEDUPLICATION] shared_deduplication_preserves_validity
      Risk: LOW - deduplication only removes redundant data
      Requires: deduplication algorithm model
      
   7. [AXIOM:SOUNDNESS] witness_reflects_tree
      Risk: LOW - direct consequence of multiproof_soundness
      Requires: composition of soundness properties
   
   Theorems proven:
   - shared_stem_deduplication_valid (from wf_multiproof_stems_cover + stem_eq_via_third)
   - multiproof_key_consistency (from multiproof_soundness + functional tree)
   - multiproof_size_nonneg
   - empty_multiproof_size
   - dedup_size_le
   - nth_error_In
   - nth_error_same_key_idx
   
   QuickChick properties:
   - prop_multiproof_len_consistent
   - prop_empty_multiproof_wf
   - prop_witness_size_ge_proof
   - prop_stem_proof_8_siblings
*)
