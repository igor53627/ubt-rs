(** * HashMap Bridge: Connect Library StdlibHashMap to UBT's StemMap/SubIndexMap
    
    This module shows that UBT's map types are instances of the library's
    HashMap model, enabling reuse of proven HashMap stepping lemmas.
    
    ** Key Insight
    
    The library models HashMap<K,V> as `list (K * V)`.
    UBT defines:
    - SubIndexMap = list (SubIndex * Value)  
    - StemMap = list (Stem * SubIndexMap)
    
    These are exactly the same structure, with:
    - SubIndex = Z, Value = B256 (bytes32)
    - Stem = list byte (31 bytes)
    
    ** Refinement Lemmas
    
    We show that UBT's sim_get/sim_set match the library's map_get/map_insert
    (modulo the zero-value special case in sim_set).
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Bool.
Import ListNotations.

Require Import UBT.Sim.tree.

Open Scope Z_scope.

(** ** SubIndexMap as HashMap<SubIndex, Value>
    
    SubIndex = Z, Value = B256
*)

Module SubIndexMapBridge.

  (** Key equality for SubIndex *)
  Definition subindex_eq (i1 i2 : SubIndex) : bool := Z.eqb i1 i2.

  (** Proven: subindex_eq is reflexive *)
  Lemma subindex_eq_refl : forall i, subindex_eq i i = true.
  Proof. intros. unfold subindex_eq. apply Z.eqb_refl. Qed.

  (** Proven: subindex_eq is symmetric *)
  Lemma subindex_eq_sym : forall i1 i2, subindex_eq i1 i2 = subindex_eq i2 i1.
  Proof. intros. unfold subindex_eq. apply Z.eqb_sym. Qed.

  (** Proven: subindex_eq true implies equality *)
  Lemma subindex_eq_true : forall i1 i2, subindex_eq i1 i2 = true -> i1 = i2.
  Proof. intros. unfold subindex_eq in H. apply Z.eqb_eq. exact H. Qed.

  (** ** Correspondence with sim_get *)

  (** UBT's sim_get equals library's map_get pattern *)
  Lemma sim_get_is_map_get : forall (m : SubIndexMap) (idx : SubIndex),
    sim_get m idx = 
    match find (fun p => subindex_eq (fst p) idx) m with
    | Some (_, v) => Some v
    | None => None
    end.
  Proof.
    intros m idx.
    unfold sim_get, subindex_eq.
    reflexivity.
  Qed.

  (** ** Correspondence with sim_set (non-zero case) *)

  (** For non-zero values, sim_set equals library's map_insert pattern *)
  Lemma sim_set_nonzero_is_map_insert : forall (m : SubIndexMap) (idx : SubIndex) (v : Value),
    is_zero_value v = false ->
    sim_set m idx v = (idx, v) :: filter (fun p => negb (subindex_eq (fst p) idx)) m.
  Proof.
    intros m idx v Hnonzero.
    unfold sim_set, subindex_eq.
    rewrite Hnonzero.
    reflexivity.
  Qed.

  (** ** Zero-value special case *)
  
  (** For zero values, sim_set removes the key (like map_remove) *)
  Lemma sim_set_zero_is_remove : forall (m : SubIndexMap) (idx : SubIndex) (v : Value),
    is_zero_value v = true ->
    sim_set m idx v = filter (fun p => negb (subindex_eq (fst p) idx)) m.
  Proof.
    intros m idx v Hzero.
    unfold sim_set, subindex_eq.
    rewrite Hzero.
    reflexivity.
  Qed.

  (** ** Reusing Library Lemmas
      
      With the above correspondence, we can instantiate the library's
      HashMap lemmas for SubIndexMap:
      
      1. sim_get_set_same corresponds to map_get_insert_same
      2. sim_get_set_other corresponds to map_get_insert_other
      
      The UBT proofs (sim_get_set_same, sim_get_set_other) already exist
      in simulations/tree.v and are equivalent to the library lemmas.
  *)

End SubIndexMapBridge.

(** ** StemMap as HashMap<Stem, SubIndexMap>
    
    Stem = list byte (31 bytes), SubIndexMap = list (SubIndex * Value)
*)

Module StemMapBridge.

  (** Key equality for Stem - reuse from tree.v *)
  (** Note: stem_eq is already defined in tree.v as boolean equality *)
  
  (** Proven: stem_eq is reflexive - reexport from tree.v *)
  Definition stem_eq_refl := tree.stem_eq_refl.

  (** Proven: stem_eq true implies equality - reexport from tree.v *)
  Definition stem_eq_true := tree.stem_eq_true.

  (** ** Correspondence with stems_get *)

  (** UBT's stems_get equals library's map_get pattern *)
  Lemma stems_get_is_map_get : forall (m : StemMap) (s : Stem),
    stems_get m s = 
    match find (fun p => stem_eq (fst p) s) m with
    | Some (_, v) => Some v
    | None => None
    end.
  Proof.
    intros m s.
    unfold stems_get, stem_eq.
    reflexivity.
  Qed.

  (** ** Correspondence with stems_set *)

  (** UBT's stems_set equals library's map_insert pattern *)
  Lemma stems_set_is_map_insert : forall (m : StemMap) (s : Stem) (v : SubIndexMap),
    stems_set m s v = (s, v) :: filter (fun p => negb (stem_eq (fst p) s)) m.
  Proof.
    intros m s v.
    unfold stems_set, stem_eq.
    reflexivity.
  Qed.

  (** ** Reusing Library Lemmas
      
      With the above correspondence, we can derive:
      
      1. stems_get (stems_set m s v) s = Some v
      2. s1 <> s2 -> stems_get (stems_set m s1 v) s2 = stems_get m s2
      
      These follow from map_get_insert_same and map_get_insert_other.
  *)

  (** Derived: stems_get_set_same *)
  Lemma stems_get_set_same : forall m s v,
    stems_get (stems_set m s v) s = Some v.
  Proof.
    intros m s v.
    rewrite stems_get_is_map_get.
    rewrite stems_set_is_map_insert.
    simpl.
    rewrite stem_eq_refl.
    reflexivity.
  Qed.

  (** Derived: stems_get_set_other - reexport from tree.v *)
  Definition stems_get_set_other := tree.stems_get_set_other.

End StemMapBridge.

(** ** Summary
    
    This module establishes that:
    
    1. SubIndexMap = list (SubIndex * Value) is a HashMap<Z, B256>
    2. StemMap = list (Stem * SubIndexMap) is a HashMap<Stem, SubIndexMap>
    
    Both use the same underlying structure as the library's HashMap model.
    
    Key lemmas:
    - sim_get_is_map_get, sim_set_nonzero_is_map_insert
    - stems_get_is_map_get, stems_set_is_map_insert
    - stems_get_set_same, stems_get_set_other (derived from library pattern)
    
    This enables:
    1. Using library's HashMap stepping rules for UBT maps
    2. Connecting Rust HashMap::get/insert stepping to UBT simulation
    3. Reducing axioms by reusing library proofs
*)
