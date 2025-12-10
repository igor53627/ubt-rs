(** * Serialization Verification Model
    
    Formal verification model for serialization/deserialization of
    proof types. This module ensures that serialization is:
    1. Round-trip safe: deserialize(serialize(x)) = Some x
    2. Canonical: serialize(x) = serialize(y) → x = y
    3. Validity-preserving: valid proofs remain valid after round-trip
    
    ** Security Considerations
    
    This model addresses critical security properties:
    
    - Malformed proof handling: Deserialization may fail (returns None)
      on malformed input, preventing invalid proofs from being processed.
      
    - DoS via oversized proofs: Size bounds are modeled via the
      [serialized_size_bounded] axiom. Implementations must validate
      size limits before deserializing to prevent memory exhaustion.
      
    - Canonical encoding prevents proof malleability attacks where
      multiple encodings of the same proof could bypass deduplication.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import UBT.Sim.tree.
Import ListNotations.

Open Scope Z_scope.

(** ** Abstract Byte Representation *)

Definition ByteString := list Byte.

(** ** Direction Serialization *)

Parameter serialize_direction : Direction -> ByteString.
Parameter deserialize_direction : ByteString -> option (Direction * ByteString).

(** [AXIOM:ROUNDTRIP] Direction round-trip property.
    Serializing and then deserializing a Direction yields the original value. *)
Axiom direction_roundtrip : forall d rest,
  deserialize_direction (serialize_direction d ++ rest) = Some (d, rest).

(** [AXIOM:CANONICAL] Direction canonical encoding.
    Equal serializations imply equal Directions. *)
Axiom direction_canonical : forall d1 d2,
  serialize_direction d1 = serialize_direction d2 -> d1 = d2.

(** Direction serialization size is 1 byte *)
Axiom direction_size : forall d,
  length (serialize_direction d) = 1%nat.

(** ** TreeKey Serialization *)

Parameter serialize_treekey : TreeKey -> ByteString.
Parameter deserialize_treekey : ByteString -> option (TreeKey * ByteString).

(** [AXIOM:ROUNDTRIP] TreeKey round-trip property. *)
Axiom treekey_roundtrip : forall k rest,
  deserialize_treekey (serialize_treekey k ++ rest) = Some (k, rest).

(** [AXIOM:CANONICAL] TreeKey canonical encoding. *)
Axiom treekey_canonical : forall k1 k2,
  serialize_treekey k1 = serialize_treekey k2 -> k1 = k2.

(** TreeKey serialization size is exactly 32 bytes (31-byte stem + 1-byte subindex) *)
Axiom treekey_size : forall k,
  length (serialize_treekey k) = 32%nat.

(** ** Stem Serialization *)

Parameter serialize_stem : Stem -> ByteString.
Parameter deserialize_stem : ByteString -> option (Stem * ByteString).

(** [AXIOM:ROUNDTRIP] Stem round-trip property. *)
Axiom stem_roundtrip : forall s rest,
  deserialize_stem (serialize_stem s ++ rest) = Some (s, rest).

(** [AXIOM:CANONICAL] Stem canonical encoding. *)
Axiom stem_canonical : forall s1 s2,
  serialize_stem s1 = serialize_stem s2 -> s1 = s2.

(** Stem serialization size is exactly 31 bytes *)
Axiom stem_serialization_size : forall s,
  length (serialize_stem s) = 31%nat.

(** ** Value (Bytes32) Serialization *)

Parameter serialize_value : Value -> ByteString.
Parameter deserialize_value : ByteString -> option (Value * ByteString).

(** [AXIOM:ROUNDTRIP] Value round-trip property. *)
Axiom value_roundtrip : forall v rest,
  deserialize_value (serialize_value v ++ rest) = Some (v, rest).

(** [AXIOM:CANONICAL] Value canonical encoding. *)
Axiom value_canonical : forall v1 v2,
  serialize_value v1 = serialize_value v2 -> v1 = v2.

(** Value serialization size is exactly 32 bytes *)
Axiom value_serialization_size : forall v,
  length (serialize_value v) = 32%nat.

(** ** Optional Value Serialization *)

Parameter serialize_option_value : option Value -> ByteString.
Parameter deserialize_option_value : ByteString -> option (option Value * ByteString).

(** [AXIOM:ROUNDTRIP] Optional value round-trip property. *)
Axiom option_value_roundtrip : forall ov rest,
  deserialize_option_value (serialize_option_value ov ++ rest) = Some (ov, rest).

(** [AXIOM:CANONICAL] Optional value canonical encoding. *)
Axiom option_value_canonical : forall ov1 ov2,
  serialize_option_value ov1 = serialize_option_value ov2 -> ov1 = ov2.

(** Optional value serialization size is 33 bytes (1 tag + 32 value, or just 1 for None) *)
Axiom option_value_size : forall ov,
  match ov with
  | Some _ => length (serialize_option_value ov) = 33%nat
  | None => length (serialize_option_value ov) = 1%nat
  end.

(** ** MerkleStep Serialization *)

Parameter serialize_merkle_step : MerkleStep -> ByteString.
Parameter deserialize_merkle_step : ByteString -> option (MerkleStep * ByteString).

(** [AXIOM:ROUNDTRIP] MerkleStep round-trip property. *)
Axiom merkle_step_roundtrip : forall ms rest,
  deserialize_merkle_step (serialize_merkle_step ms ++ rest) = Some (ms, rest).

(** [AXIOM:CANONICAL] MerkleStep canonical encoding. *)
Axiom merkle_step_canonical : forall ms1 ms2,
  serialize_merkle_step ms1 = serialize_merkle_step ms2 -> ms1 = ms2.

(** MerkleStep size is 33 bytes (32-byte sibling + 1-byte direction) *)
Axiom merkle_step_size : forall ms,
  length (serialize_merkle_step ms) = 33%nat.

(** ** MerkleWitness (list of MerkleStep) Serialization *)

Parameter serialize_merkle_witness : MerkleWitness -> ByteString.
Parameter deserialize_merkle_witness : ByteString -> option (MerkleWitness * ByteString).

(** [AXIOM:ROUNDTRIP] MerkleWitness round-trip property. *)
Axiom merkle_witness_roundtrip : forall mw rest,
  deserialize_merkle_witness (serialize_merkle_witness mw ++ rest) = Some (mw, rest).

(** [AXIOM:CANONICAL] MerkleWitness canonical encoding. *)
Axiom merkle_witness_canonical : forall mw1 mw2,
  serialize_merkle_witness mw1 = serialize_merkle_witness mw2 -> mw1 = mw2.

(** MerkleWitness size depends on number of steps *)
Axiom merkle_witness_size : forall mw,
  length (serialize_merkle_witness mw) = (4 + length mw * 33)%nat.

(** ** InclusionProof Serialization *)

Parameter serialize_inclusion_proof : InclusionProof -> ByteString.
Parameter deserialize_inclusion_proof : ByteString -> option (InclusionProof * ByteString).

(** [AXIOM:ROUNDTRIP] InclusionProof round-trip property. *)
Axiom inclusion_proof_roundtrip : forall p rest,
  deserialize_inclusion_proof (serialize_inclusion_proof p ++ rest) = Some (p, rest).

(** [AXIOM:CANONICAL] InclusionProof canonical encoding. *)
Axiom inclusion_proof_canonical : forall p1 p2,
  serialize_inclusion_proof p1 = serialize_inclusion_proof p2 -> p1 = p2.

(** ** ExclusionProof Serialization *)

Parameter serialize_exclusion_proof : ExclusionProof -> ByteString.
Parameter deserialize_exclusion_proof : ByteString -> option (ExclusionProof * ByteString).

(** [AXIOM:ROUNDTRIP] ExclusionProof round-trip property. *)
Axiom exclusion_proof_roundtrip : forall p rest,
  deserialize_exclusion_proof (serialize_exclusion_proof p ++ rest) = Some (p, rest).

(** [AXIOM:CANONICAL] ExclusionProof canonical encoding. *)
Axiom exclusion_proof_canonical : forall p1 p2,
  serialize_exclusion_proof p1 = serialize_exclusion_proof p2 -> p1 = p2.

(** ** MultiProof Serialization *)

Parameter serialize_multiproof : MultiProof -> ByteString.
Parameter deserialize_multiproof : ByteString -> option (MultiProof * ByteString).

(** [AXIOM:ROUNDTRIP] MultiProof round-trip property. *)
Axiom multiproof_roundtrip : forall mp rest,
  deserialize_multiproof (serialize_multiproof mp ++ rest) = Some (mp, rest).

(** [AXIOM:CANONICAL] MultiProof canonical encoding. *)
Axiom multiproof_canonical : forall mp1 mp2,
  serialize_multiproof mp1 = serialize_multiproof mp2 -> mp1 = mp2.

(** MultiProof size matches the formula from proof.rs *)
Axiom multiproof_serialization_size : forall mp,
  length (serialize_multiproof mp) = 
    (16 + (* 4 length fields *)
     length (mp_keys mp) * 32 +
     length (mp_values mp) * 33 +
     length (mp_nodes mp) * 32 +
     length (mp_stems mp) * 31)%nat.

(** ** Proof Validity Preservation *)

(** [THEOREM] Serialization preserves inclusion proof validity.
    A valid inclusion proof remains valid after serialization round-trip. *)
Theorem serialize_preserves_inclusion_validity :
  forall (p : InclusionProof) (root : Bytes32) (p' : InclusionProof) rest,
    verify_inclusion_proof p root ->
    deserialize_inclusion_proof (serialize_inclusion_proof p ++ rest) = Some (p', rest) ->
    verify_inclusion_proof p' root.
Proof.
  intros p root p' rest Hvalid Hdeser.
  rewrite inclusion_proof_roundtrip in Hdeser.
  injection Hdeser as Hp Hrest.
  subst p'.
  exact Hvalid.
Qed.

(** [THEOREM] Serialization preserves exclusion proof validity. *)
Theorem serialize_preserves_exclusion_validity :
  forall (p : ExclusionProof) (root : Bytes32) (p' : ExclusionProof) rest,
    verify_exclusion_proof p root ->
    deserialize_exclusion_proof (serialize_exclusion_proof p ++ rest) = Some (p', rest) ->
    verify_exclusion_proof p' root.
Proof.
  intros p root p' rest Hvalid Hdeser.
  rewrite exclusion_proof_roundtrip in Hdeser.
  injection Hdeser as Hp Hrest.
  subst p'.
  exact Hvalid.
Qed.

(** [THEOREM] Serialization preserves multiproof validity. *)
Theorem serialize_preserves_multiproof_validity :
  forall (mp : MultiProof) (root : Bytes32) (mp' : MultiProof) rest,
    verify_multiproof mp root ->
    deserialize_multiproof (serialize_multiproof mp ++ rest) = Some (mp', rest) ->
    verify_multiproof mp' root.
Proof.
  intros mp root mp' rest Hvalid Hdeser.
  rewrite multiproof_roundtrip in Hdeser.
  injection Hdeser as Hmp Hrest.
  subst mp'.
  exact Hvalid.
Qed.

(** ** Size Bounds for DoS Prevention *)

(** Maximum allowed proof size (configurable per deployment) *)
Parameter MAX_PROOF_SIZE : nat.

(** Size bound invariant: proofs must be within size limits *)
Definition proof_size_bounded (mp : MultiProof) : Prop :=
  length (serialize_multiproof mp) <= MAX_PROOF_SIZE.

(** [AXIOM:SECURITY] Serialized size is bounded by computed proof size.
    The actual serialized bytes are bounded by the multiproof_size function
    from tree.v plus a constant overhead for length encoding.
    
    This enables implementations to reject oversized proofs before
    full deserialization, preventing memory exhaustion attacks. *)
Axiom serialized_size_bounded : forall mp,
  length (serialize_multiproof mp) <= multiproof_size mp + 16.

(** Corollary: proof size can be checked before deserialization *)
Lemma proof_size_checkable : forall mp,
  multiproof_size mp + 16 <= MAX_PROOF_SIZE ->
  proof_size_bounded mp.
Proof.
  intros mp Hbound.
  unfold proof_size_bounded.
  pose proof (serialized_size_bounded mp).
  lia.
Qed.

(** ** Malformed Input Handling *)

(** Deserialization of truncated input fails *)
Axiom deserialize_truncated_fails : forall (bs : ByteString),
  length bs < 16 ->
  deserialize_multiproof bs = None.

(** Deserialization with invalid tag fails *)
Definition is_valid_option_tag (b : Byte) : bool :=
  Z.eqb b 0 || Z.eqb b 1.

(** [AXIOM:SECURITY] Invalid option tags cause deserialization failure.
    This prevents malformed proofs with invalid tags from being accepted. *)
Axiom invalid_tag_fails : forall bs tag rest,
  bs = tag :: rest ->
  is_valid_option_tag tag = false ->
  deserialize_option_value bs = None.

(** ** Proof Size Consistency *)

(** [THEOREM] Computed proof size matches serialized size.
    The size() method in Rust proof types accurately predicts
    the actual serialized byte count (within constant overhead). *)
Theorem proof_size_matches_serialized : forall mp,
  wf_multiproof mp ->
  length (serialize_multiproof mp) <= multiproof_size mp + 16 /\
  multiproof_size mp <= length (serialize_multiproof mp).
Proof.
  intros mp Hwf.
  split.
  - apply serialized_size_bounded.
  - rewrite multiproof_serialization_size.
    unfold multiproof_size.
    lia.
Qed.

(** ** Deterministic Serialization *)

(** [AXIOM:DETERMINISM] Serialization is deterministic.
    The same value always produces the same byte sequence. *)
Axiom serialize_deterministic : forall mp1 mp2,
  mp1 = mp2 -> serialize_multiproof mp1 = serialize_multiproof mp2.

(** Contrapositive: different byte sequences imply different values *)
Lemma serialize_injective_contra : forall mp1 mp2,
  serialize_multiproof mp1 <> serialize_multiproof mp2 ->
  mp1 <> mp2.
Proof.
  intros mp1 mp2 Hneq Heq.
  apply Hneq.
  apply serialize_deterministic.
  exact Heq.
Qed.

(** ** Cross-Type Serialization Properties *)

(** Inclusion and exclusion proofs have disjoint serialization formats *)
Axiom inclusion_exclusion_disjoint : forall ip ep,
  serialize_inclusion_proof ip <> serialize_exclusion_proof ep.

(** Empty multiproof serialization *)
Lemma empty_multiproof_serializes : 
  exists bs, serialize_multiproof empty_multiproof = bs /\ length bs = 16%nat.
Proof.
  exists (serialize_multiproof empty_multiproof).
  split; [reflexivity|].
  rewrite multiproof_serialization_size.
  unfold empty_multiproof. simpl.
  reflexivity.
Qed.

(** ** Batch Serialization *)

(** Serialize a list of inclusion proofs *)
Fixpoint serialize_batch_inclusion (batch : BatchInclusionProof) : ByteString :=
  match batch with
  | [] => []
  | p :: rest => serialize_inclusion_proof p ++ serialize_batch_inclusion rest
  end.

(** Deserialize a list of inclusion proofs *)
Fixpoint deserialize_batch_inclusion (n : nat) (bs : ByteString) 
  : option (BatchInclusionProof * ByteString) :=
  match n with
  | O => Some ([], bs)
  | S m => 
      match deserialize_inclusion_proof bs with
      | None => None
      | Some (p, rest) =>
          match deserialize_batch_inclusion m rest with
          | None => None
          | Some (ps, rest') => Some (p :: ps, rest')
          end
      end
  end.

(** [THEOREM] Batch serialization round-trip. *)
Theorem batch_inclusion_roundtrip : forall batch rest,
  deserialize_batch_inclusion (length batch) (serialize_batch_inclusion batch ++ rest) = 
    Some (batch, rest).
Proof.
  induction batch as [|p rest_batch IH]; intros rest.
  - simpl. reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite inclusion_proof_roundtrip.
    rewrite IH.
    reflexivity.
Qed.

(** ** Summary of Security Properties
    
    1. ROUND-TRIP SAFETY
       All proof types satisfy: deserialize(serialize(x)) = Some x
       This ensures no data loss through serialization.
    
    2. CANONICAL ENCODING
       All proof types satisfy: serialize(x) = serialize(y) → x = y
       This prevents proof malleability attacks.
    
    3. VALIDITY PRESERVATION
       Valid proofs remain valid after round-trip serialization.
       Attackers cannot invalidate proofs through serialization.
    
    4. SIZE BOUNDS
       Serialized size is bounded and checkable before deserialization.
       This enables DoS prevention without full parsing.
    
    5. MALFORMED INPUT REJECTION
       Invalid inputs (truncated, bad tags) cause deserialization to
       return None, preventing processing of malformed proofs.
    
    6. DETERMINISTIC OUTPUT
       Same value always produces same bytes, enabling caching and
       deduplication of serialized proofs.
*)
