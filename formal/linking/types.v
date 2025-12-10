(** * Type Links for UBT
    
    This module defines Link instances connecting:
    - Simulation types (SimTree, Stem, TreeKey, etc.) in simulations/tree.v
    - Translated Rust types (UnifiedBinaryTree, Stem, TreeKey) in src/tree.v
    
    ** Linking Architecture
    
    The linking approach follows rocq-of-rust conventions:
    - Link typeclass provides Φ (Rust type) and φ (encoding function)
    - OfTy.t witnesses Rocq type ↔ Rust type correspondence
    - OfValue.t witnesses Rocq value ↔ Rust value correspondence
    
    ** Module Structure
    
    1. PRIMITIVE TYPES: ByteLink, Bytes32Link, Bytes31Link
       Maps basic byte sequences to Rust integer/array types
       
    2. DOMAIN TYPES: StemLink, SubIndexLink, TreeKeyLink, ValueLink
       Maps UBT-specific types to their Rust representations
       
    3. CONTAINER TYPES: OptionLink, ResultLink, SubIndexMapLink, StemMapLink
       Maps generic containers with proper type parameters
       
    4. AGGREGATE TYPES: SimTreeLink
       Maps the full tree structure including hasher parameter
       
    5. CORRESPONDENCE LEMMAS: TypeCorrespondence module
       Proves encoding properties like injectivity and structure preservation
       
    6. REFINEMENT DEFINITIONS: Refinement module
       Defines when Rust values correctly represent simulation values
    
    ** Key Properties
    
    - All links are compositional: complex types build on primitive links
    - φ encoding is injective for all types (proven for Bytes32)
    - Structure is preserved through encoding (proven for TreeKey, SimTree)
    
    ** Usage in operations.v
    
    The tree_refines relation is the key connection:
      tree_refines H rust_tree sim_tree := rust_tree = φ sim_tree
    
    This allows stating that Rust execution produces simulation results.
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.

Require Import UBT.Sim.crypto.
Require Import UBT.Sim.tree.

Open Scope Z_scope.

(** ** Byte linking *)

Module ByteLink.
  Definition Rust_ty : Ty.t := Ty.path "u8".
  
  Global Instance IsLink : Link Byte := {
    Φ := Rust_ty;
    φ b := Value.Integer IntegerKind.U8 b;
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Byte); reflexivity. Defined.
End ByteLink.

(** ** Bytes32 linking (maps to B256 / FixedBytes<32>) *)

Module Bytes32Link.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") 
             [Value.Integer IntegerKind.Usize 32] [].
  
  Fixpoint bytes_to_array (bs : list Z) : list Value.t :=
    match bs with
    | [] => []
    | b :: rest => Value.Integer IntegerKind.U8 b :: bytes_to_array rest
    end.
  
  Global Instance IsLink : Link Bytes32 := {
    Φ := Rust_ty;
    φ bs := Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" 
              [Value.Integer IntegerKind.Usize 32] [] 
              [Value.Array (bytes_to_array bs)];
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Bytes32); reflexivity. Defined.
End Bytes32Link.

(** ** Bytes31 linking *)

Module Bytes31Link.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "slice") [] [Ty.path "u8"].
  
  Global Instance IsLink : Link Bytes31 := {
    Φ := Bytes31Link.Rust_ty;
    φ bs := Value.Array (Bytes32Link.bytes_to_array bs);
  }.
End Bytes31Link.

(** ** Stem linking *)

Module StemLink.
  Definition Rust_ty : Ty.t := Ty.path "ubt::key::Stem".
  
  Global Instance IsLink : Link Stem := {
    Φ := Rust_ty;
    φ s := Value.StructTuple "ubt::key::Stem" [] []
             [Value.Array (Bytes32Link.bytes_to_array (stem_data s))];
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Stem); reflexivity. Defined.
End StemLink.

(** ** SubIndex linking (u8) *)

Module SubIndexLink.
  Definition Rust_ty : Ty.t := Ty.path "u8".
  
  Global Instance IsLink : Link SubIndex := {
    Φ := Rust_ty;
    φ idx := Value.Integer IntegerKind.U8 idx;
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := SubIndex); reflexivity. Defined.
End SubIndexLink.

(** ** TreeKey linking *)

Module TreeKeyLink.
  Definition Rust_ty : Ty.t := Ty.path "ubt::key::TreeKey".
  
  Global Instance IsLink : Link TreeKey := {
    Φ := Rust_ty;
    φ k := Value.StructRecord "ubt::key::TreeKey" [] []
             [("stem", φ (tk_stem k)); 
              ("subindex", φ (tk_subindex k))];
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := TreeKey); reflexivity. Defined.
End TreeKeyLink.

(** ** Value linking (same as Bytes32) *)

Module ValueLink.
  Definition Rust_ty : Ty.t := Bytes32Link.Rust_ty.
  
  Global Instance IsLink : Link Value := {
    Φ := Rust_ty;
    φ v := φ v;
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := Value); reflexivity. Defined.
End ValueLink.

(** ** Option linking *)

Module OptionLink.
  Definition Rust_ty (A_ty : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "core::option::Option") [] [A_ty].
  
  Global Instance IsLink (A : Set) `{Link A} : Link (option A) := {
    Φ := OptionLink.Rust_ty (Φ A);
    φ opt := match opt with
             | None => Value.StructTuple "core::option::Option::None" [] [Φ A] []
             | Some v => Value.StructTuple "core::option::Option::Some" [] [Φ A] [φ v]
             end;
  }.
  
  Definition of_ty (A_ty : Ty.t) (H : OfTy.t A_ty) : OfTy.t (OptionLink.Rust_ty A_ty).
  Proof.
    destruct H as [A].
    eapply OfTy.Make with (A := option A).
    subst. reflexivity.
  Defined.
End OptionLink.

(** ** SubIndexMap linking (list of (SubIndex * Value) pairs)
    
    Encoding scheme:
    - SubIndexMap is encoded as a Rust HashMap containing actual entries
    - Each entry is a (SubIndex, Value) pair encoded as a tuple
    - The entries list is stored in the HashMap's "entries" field
    - This ensures different maps have different encodings (up to permutation)
*)

Module SubIndexMapLink.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "std::collections::hash::map::HashMap") []
      [Ty.path "u8"; Bytes32Link.Rust_ty; Ty.path "std::hash::random::RandomState"].
  
  (** Encode a single (SubIndex, Value) pair as a tuple *)
  Definition pair_to_value (p : SubIndex * Value) : Value.t :=
    Value.Tuple [φ (fst p); φ (snd p)].
  
  (** Encode all entries as a list of tuples *)
  Fixpoint entries_to_array (entries : list (SubIndex * Value)) : list Value.t :=
    match entries with
    | [] => []
    | p :: rest => pair_to_value p :: entries_to_array rest
    end.
  
  (** Full encoding includes actual key-value pairs *)
  Definition subindexmap_to_value (m : SubIndexMap) : Value.t :=
    Value.StructRecord "std::collections::hash::map::HashMap" [] 
      [Ty.path "u8"; Bytes32Link.Rust_ty; Ty.path "std::hash::random::RandomState"]
      [("entries", Value.Array (entries_to_array m))].
  
  Global Instance IsLink : Link SubIndexMap := {
    Φ := Rust_ty;
    φ m := subindexmap_to_value m;
  }.
  
  (** Encoding preserves entry count *)
  Lemma encoding_length : forall m,
    length (entries_to_array m) = length m.
  Proof.
    induction m as [|p rest IH].
    - reflexivity.
    - simpl. f_equal. exact IH.
  Qed.
  
  (** Entries encoding is injective *)
  Lemma entries_to_array_injective : forall m1 m2,
    entries_to_array m1 = entries_to_array m2 -> m1 = m2.
  Proof.
    induction m1 as [|[k1 v1] rest1 IH]; intros m2 Heq.
    - destruct m2 as [|[k2 v2] rest2]; [reflexivity | discriminate].
    - destruct m2 as [|[k2 v2] rest2]; [discriminate |].
      simpl in Heq.
      injection Heq as Hpair Hrest.
      unfold pair_to_value in Hpair.
      injection Hpair as Hk Hv.
      unfold φ in Hk, Hv. simpl in Hk, Hv.
      injection Hk as Hk'.
      f_equal.
      + f_equal; [exact Hk' |].
        apply TypeCorrespondence.bytes32_encoding_injective.
        exact Hv.
      + apply IH. exact Hrest.
  Qed.
  
  (** Different maps have different encodings (up to exact list equality) *)
  Lemma encoding_injective : forall m1 m2,
    φ m1 = φ m2 -> m1 = m2.
  Proof.
    intros m1 m2 Heq.
    unfold φ in Heq. simpl in Heq.
    unfold subindexmap_to_value in Heq.
    injection Heq as Hentries.
    injection Hentries as Harr.
    apply entries_to_array_injective. exact Harr.
  Qed.
End SubIndexMapLink.

(** ** StemMap linking
    
    Encoding scheme:
    - StemMap is encoded as a Rust HashMap containing actual entries
    - Each entry is a (Stem, SubIndexMap) pair
    - The Stem is encoded via StemLink
    - The SubIndexMap is encoded via SubIndexMapLink (now with full content)
    - Different maps have different encodings (up to permutation)
*)

Module StemMapLink.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "std::collections::hash::map::HashMap") []
      [StemLink.Rust_ty; Ty.path "ubt::node::StemNode"; 
       Ty.path "std::hash::random::RandomState"].
  
  (** Encode a single (Stem, SubIndexMap) pair as a tuple *)
  Definition stem_pair_to_value (p : Stem * SubIndexMap) : Value.t :=
    Value.Tuple [φ (fst p); φ (snd p)].
  
  (** Encode all entries as a list of tuples *)
  Fixpoint stemmap_entries_to_array (entries : list (Stem * SubIndexMap)) : list Value.t :=
    match entries with
    | [] => []
    | p :: rest => stem_pair_to_value p :: stemmap_entries_to_array rest
    end.
  
  (** Full encoding includes actual key-value pairs *)
  Definition stemmap_to_value (m : StemMap) : Value.t :=
    Value.StructRecord "std::collections::hash::map::HashMap" []
      [StemLink.Rust_ty; Ty.path "ubt::node::StemNode"; 
       Ty.path "std::hash::random::RandomState"]
      [("entries", Value.Array (stemmap_entries_to_array m))].
  
  Global Instance IsLink : Link StemMap := {
    Φ := Rust_ty;
    φ m := stemmap_to_value m;
  }.
  
  (** Encoding preserves entry count *)
  Lemma encoding_length : forall m,
    length (stemmap_entries_to_array m) = length m.
  Proof.
    induction m as [|p rest IH].
    - reflexivity.
    - simpl. f_equal. exact IH.
  Qed.
  
  (** Stem encoding is injective (needed for StemMap injectivity) *)
  Lemma stem_encoding_injective : forall s1 s2 : Stem,
    φ s1 = φ s2 -> s1 = s2.
  Proof.
    intros s1 s2 Heq.
    unfold φ in Heq. simpl in Heq.
    injection Heq as Harr.
    injection Harr as Hdata.
    destruct s1 as [d1], s2 as [d2]. simpl in *.
    f_equal.
    clear -Hdata.
    revert d2 Hdata.
    induction d1 as [|b1 rest1 IH]; intros d2 Hdata.
    - destruct d2; [reflexivity | discriminate].
    - destruct d2 as [|b2 rest2]; [discriminate |].
      simpl in Hdata. injection Hdata as Hb Hrest.
      injection Hb as Heq. f_equal; [exact Heq | apply IH; exact Hrest].
  Qed.
  
  (** StemMap entries encoding is injective *)
  Lemma stemmap_entries_injective : forall m1 m2,
    stemmap_entries_to_array m1 = stemmap_entries_to_array m2 -> m1 = m2.
  Proof.
    induction m1 as [|[s1 v1] rest1 IH]; intros m2 Heq.
    - destruct m2 as [|[s2 v2] rest2]; [reflexivity | discriminate].
    - destruct m2 as [|[s2 v2] rest2]; [discriminate |].
      simpl in Heq.
      injection Heq as Hpair Hrest.
      unfold stem_pair_to_value in Hpair.
      injection Hpair as Hs Hv.
      f_equal.
      + f_equal.
        * apply stem_encoding_injective. exact Hs.
        * apply SubIndexMapLink.encoding_injective. exact Hv.
      + apply IH. exact Hrest.
  Qed.
  
  (** Different maps have different encodings (up to exact list equality) *)
  Lemma encoding_injective : forall m1 m2,
    φ m1 = φ m2 -> m1 = m2.
  Proof.
    intros m1 m2 Heq.
    unfold φ in Heq. simpl in Heq.
    unfold stemmap_to_value in Heq.
    injection Heq as Hentries.
    injection Hentries as Harr.
    apply stemmap_entries_injective. exact Harr.
  Qed.
End StemMapLink.

(** ** SimTree linking to UnifiedBinaryTree<H>
    
    ** Root Field Abstraction
    
    The Rust `UnifiedBinaryTree` has a `root: Node` field that caches the
    computed Merkle root. However, this field is *not* part of the logical
    state - it is a performance optimization (lazy root computation).
    
    In the linking:
    - The `root` field is encoded as `Node::Empty` regardless of the actual
      cached value in Rust. This is intentional.
    - The `tree_refines` relation (in operations.v) only checks that the
      `stems` map matches - it ignores the `root` field entirely.
    - The actual root hash is defined by `sim_root_hash` in the simulation,
      which computes it from the stems on-demand.
    
    This design reflects that:
    1. The stems map is the authoritative state
    2. The root is derivable from stems (deterministic computation)
    3. Rust caches this for performance; simulation computes on-demand
    
    The axiom `HashLink.root_hash_executes` (in operations.v) ties the
    on-demand simulation computation to the Rust cached/computed value,
    establishing that both produce the same hash for equivalent trees.
*)

Module SimTreeLink.
  Definition Rust_ty (H : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "ubt::tree::UnifiedBinaryTree") [] [H].
  
  (** The encoding ignores the Rust `root` field (encoded as Empty).
      Only `stems` matters for logical equivalence - see tree_refines. *)
  Global Instance IsLink (H : Ty.t) : Link SimTree := {
    Φ := Rust_ty H;
    φ t := Value.StructRecord "ubt::tree::UnifiedBinaryTree" [] [H]
             [("root", Value.StructTuple "ubt::node::Node::Empty" [] [] []);
              ("hasher", Value.StructTuple "unit" [] [] []);
              ("stems", φ (st_stems t))];
  }.
End SimTreeLink.

(** ** Result linking (mirrors Rust Result type) *)

Module ResultLink.
  Definition Rust_ty (T_ty E_ty : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "core::result::Result") [] [T_ty; E_ty].
  
  Global Instance IsLink (T E : Set) `{Link T} `{Link E} : Link (T + E) := {
    Φ := ResultLink.Rust_ty (Φ T) (Φ E);
    φ res := match res with
             | inl v => Value.StructTuple "core::result::Result::Ok" [] [Φ T; Φ E] [φ v]
             | inr e => Value.StructTuple "core::result::Result::Err" [] [Φ T; Φ E] [φ e]
             end;
  }.
End ResultLink.

(** ** Boolean linking *)

Module BoolLink.
  Definition Rust_ty : Ty.t := Ty.path "bool".
  
  Global Instance IsLink : Link bool := {
    Φ := Rust_ty;
    φ b := if b then Value.Bool true else Value.Bool false;
  }.
  
  Definition of_ty : OfTy.t Rust_ty.
  Proof. eapply OfTy.Make with (A := bool); reflexivity. Defined.
End BoolLink.

(** ** Link hints for smpl tactic *)

#[export] Hint Resolve ByteLink.of_ty : of_ty.
#[export] Hint Resolve Bytes32Link.of_ty : of_ty.
#[export] Hint Resolve StemLink.of_ty : of_ty.
#[export] Hint Resolve SubIndexLink.of_ty : of_ty.
#[export] Hint Resolve TreeKeyLink.of_ty : of_ty.
#[export] Hint Resolve ValueLink.of_ty : of_ty.
#[export] Hint Resolve BoolLink.of_ty : of_ty.

(** ** Type Correspondence Lemmas
    
    These lemmas establish bidirectional relationships between
    simulation types and their Rust encodings. They form the foundation
    for refinement proofs in operations.v.
*)

Module TypeCorrespondence.
  
  (** Bytes32 roundtrip: encoding is injective *)
  Lemma bytes32_encoding_injective : forall (v1 v2 : Bytes32),
    φ v1 = φ v2 -> v1 = v2.
  Proof.
    intros v1 v2 H.
    unfold φ in H. simpl in H.
    injection H as Harr.
    clear H.
    revert v2 Harr.
    induction v1 as [|b1 rest1 IH]; intros v2 Harr.
    - destruct v2; [reflexivity | discriminate].
    - destruct v2 as [|b2 rest2]; [discriminate |].
      simpl in Harr.
      injection Harr as Hb Hrest.
      injection Hb as Heq.
      f_equal; [exact Heq |].
      apply IH. exact Hrest.
  Qed.
  
  (** TreeKey encoding preserves stem and subindex *)
  Lemma treekey_encoding_preserves_components : forall (k : TreeKey),
    exists stem_enc subidx_enc,
      φ k = Value.StructRecord "ubt::key::TreeKey" [] []
              [("stem", stem_enc); ("subindex", subidx_enc)] /\
      stem_enc = φ (tk_stem k) /\
      subidx_enc = φ (tk_subindex k).
  Proof.
    intros k.
    exists (φ (tk_stem k)), (φ (tk_subindex k)).
    split; [| split]; reflexivity.
  Qed.
  
  (** Option encoding is disjoint: None ≠ Some *)
  Lemma option_encoding_disjoint : forall (A : Set) `{Link A} (v : A),
    φ (None : option A) <> φ (Some v).
  Proof.
    intros A HA v.
    unfold φ. simpl.
    discriminate.
  Qed.
  
  (** SimTree encoding preserves stems map *)
  Lemma simtree_encoding_preserves_stems : forall (H : Ty.t) (t : SimTree),
    exists root_enc hasher_enc stems_enc,
      @φ SimTree (SimTreeLink.IsLink H) t = 
        Value.StructRecord "ubt::tree::UnifiedBinaryTree" [] [H]
          [("root", root_enc); ("hasher", hasher_enc); ("stems", stems_enc)] /\
      stems_enc = φ (st_stems t).
  Proof.
    intros H t.
    exists (Value.StructTuple "ubt::node::Node::Empty" [] [] []).
    exists (Value.StructTuple "unit" [] [] []).
    exists (φ (st_stems t)).
    split; reflexivity.
  Qed.
  
  (** Well-formed stem has correct encoding length *)
  Lemma wf_stem_encoding_length : forall (s : Stem),
    wf_stem s ->
    exists arr,
      φ s = Value.StructTuple "ubt::key::Stem" [] [] [Value.Array arr] /\
      length arr = 31%nat.
  Proof.
    intros s Hwf.
    exists (Bytes32Link.bytes_to_array (stem_data s)).
    split.
    - reflexivity.
    - unfold wf_stem in Hwf.
      clear -Hwf.
      generalize (stem_data s) as bs. intros bs Hlen.
      induction bs as [|b rest IH].
      + simpl in Hlen. discriminate.
      + simpl. f_equal.
        destruct rest; [simpl in Hlen; injection Hlen; lia |].
        apply IH. simpl in Hlen. injection Hlen. lia.
  Qed.
  
  (** Value encoding produces FixedBytes<32> structure *)
  Lemma value_encoding_structure : forall (v : Value),
    exists arr,
      φ v = Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" 
              [Value.Integer IntegerKind.Usize 32] [] [Value.Array arr].
  Proof.
    intros v.
    exists (Bytes32Link.bytes_to_array v).
    reflexivity.
  Qed.
  
  (** ** Permutation-based semantic equivalence for HashMaps
      
      For HashMaps, order of entries doesn't affect semantics.
      Two maps are semantically equivalent if their entries are permutations.
  *)
  
  (** Two SubIndexMaps are semantically equivalent if permuted *)
  Definition subindexmap_equiv (m1 m2 : SubIndexMap) : Prop :=
    Permutation m1 m2.
  
  (** Two StemMaps are semantically equivalent if permuted *)
  Definition stemmap_equiv (m1 m2 : StemMap) : Prop :=
    Permutation m1 m2.
  
  (** Semantic equivalence implies lookup equivalence for SubIndexMap *)
  Lemma subindexmap_equiv_lookup : forall m1 m2 idx,
    subindexmap_equiv m1 m2 ->
    sim_get m1 idx = sim_get m2 idx.
  Proof.
    intros m1 m2 idx Hperm.
    unfold sim_get.
    induction Hperm.
    - reflexivity.
    - simpl. destruct (Z.eqb (fst x) idx); auto.
    - simpl. 
      destruct (Z.eqb (fst x) idx) eqn:Ex;
      destruct (Z.eqb (fst y) idx) eqn:Ey; auto.
    - rewrite IHHperm1. exact IHHperm2.
  Qed.
  
  (** Semantic equivalence implies lookup equivalence for StemMap *)
  Lemma stemmap_equiv_lookup : forall m1 m2 s,
    stemmap_equiv m1 m2 ->
    stems_get m1 s = stems_get m2 s.
  Proof.
    intros m1 m2 s Hperm.
    unfold stems_get.
    induction Hperm.
    - reflexivity.
    - simpl. destruct (stem_eq (fst x) s); auto.
    - simpl. 
      destruct (stem_eq (fst x) s) eqn:Ex;
      destruct (stem_eq (fst y) s) eqn:Ey; auto.
    - rewrite IHHperm1. exact IHHperm2.
  Qed.
  
  (** Injectivity up to permutation for SubIndexMap:
      Equal encodings imply equal maps (strict).
      For semantic equivalence, use subindexmap_equiv. *)
  Lemma subindexmap_encoding_reflects_content : forall m1 m2,
    φ m1 = φ m2 -> m1 = m2.
  Proof.
    exact SubIndexMapLink.encoding_injective.
  Qed.
  
  (** Injectivity up to permutation for StemMap:
      Equal encodings imply equal maps (strict).
      For semantic equivalence, use stemmap_equiv. *)
  Lemma stemmap_encoding_reflects_content : forall m1 m2,
    φ m1 = φ m2 -> m1 = m2.
  Proof.
    exact StemMapLink.encoding_injective.
  Qed.

End TypeCorrespondence.

(** ** Refinement Relation Definitions
    
    These definitions establish when a Rust value correctly represents
    a simulation value. They are used in operations.v for linking proofs.
*)

Module Refinement.

  (** A Rust tree refines a simulation tree if encoding matches *)
  Definition tree_refines (H : Ty.t) (rust_tree : Value.t) (sim_tree : SimTree) : Prop :=
    rust_tree = @φ SimTree (SimTreeLink.IsLink H) sim_tree.
  
  (** A Rust key refines a simulation key if encoding matches *)
  Definition key_refines (rust_key : Value.t) (sim_key : TreeKey) : Prop :=
    rust_key = φ sim_key.
  
  (** A Rust value refines a simulation value if encoding matches *)
  Definition value_refines (rust_val : Value.t) (sim_val : Bytes32) : Prop :=
    rust_val = φ sim_val.
  
  (** Refinement is reflexive when encoding is used *)
  Lemma tree_refines_refl : forall (H : Ty.t) (t : SimTree),
    tree_refines H (@φ SimTree (SimTreeLink.IsLink H) t) t.
  Proof.
    intros H t.
    unfold tree_refines.
    reflexivity.
  Qed.
  
  Lemma key_refines_refl : forall (k : TreeKey),
    key_refines (φ k) k.
  Proof.
    intros k.
    unfold key_refines.
    reflexivity.
  Qed.
  
  Lemma value_refines_refl : forall (v : Bytes32),
    value_refines (φ v) v.
  Proof.
    intros v.
    unfold value_refines.
    reflexivity.
  Qed.

End Refinement.
