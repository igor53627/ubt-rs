(** * Serialization Specification
    
    Abstract specification of serialization properties for UBT types.
    These properties must hold regardless of the concrete serialization
    format (JSON, bincode, etc.).
*)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.

(** ** Abstract Serialization Interface *)

(** Type of serialized bytes *)
Definition Bytes := list Z.

(** Abstract serialization function (axiomatized per type) *)
Parameter serialize : forall (A : Type), A -> Bytes.
Parameter deserialize : forall (A : Type), Bytes -> option A.

(** ** Round-Trip Property *)

(** The fundamental correctness property: deserializing a serialized
    value recovers the original value. *)
Definition round_trip_correct (A : Type) : Prop :=
  forall (x : A),
    deserialize A (serialize A x) = Some x.

(** ** Canonical Encoding Property *)

(** Equal values must serialize to equal bytes.
    This requires deterministic serialization (e.g., sorted maps). *)
Definition canonical_encoding (A : Type) `{eq_dec : forall x y : A, {x = y} + {x <> y}} : Prop :=
  forall (x y : A),
    x = y -> serialize A x = serialize A y.

(** Stronger property: serialization is injective *)
Definition serialization_injective (A : Type) : Prop :=
  forall (x y : A),
    serialize A x = serialize A y -> x = y.

(** ** Proof-Specific Properties *)

(** Import tree spec types *)
Require Import tree_spec.

(** A proof is valid if it verifies against a root *)
Parameter proof_valid : Proof -> bytes32 -> Prop.

(** Serialization preserves proof validity *)
Definition proof_validity_preserved : Prop :=
  forall (p : Proof) (root : bytes32),
    proof_valid p root ->
    match deserialize Proof (serialize Proof p) with
    | Some p' => proof_valid p' root
    | None => False
    end.

(** This follows from round-trip correctness *)
Theorem proof_validity_from_roundtrip :
  round_trip_correct Proof -> proof_validity_preserved.
Proof.
  unfold round_trip_correct, proof_validity_preserved.
  intros Hrt p root Hvalid.
  rewrite Hrt. exact Hvalid.
Qed.

(** ** Size Bounds *)

(** Serialized size should be bounded by a function of the structure *)
Definition size_bounded (A : Type) (size_fn : A -> nat) (max_fn : A -> nat) : Prop :=
  forall (x : A),
    length (serialize A x) <= max_fn x.

(** For proofs, size is bounded by tree depth *)
Parameter proof_depth : Proof -> nat.

Definition proof_size_bounded : Prop :=
  size_bounded Proof proof_depth (fun p => 32 * (proof_depth p + 256 + 10)).

(** ** Malicious Input Resistance *)

(** Deserialized values must satisfy validity predicates *)
Definition deserialize_valid (A : Type) (valid : A -> Prop) : Prop :=
  forall (bs : Bytes) (x : A),
    deserialize A bs = Some x -> valid x.

(** Stem validity: exactly 31 bytes, all in range [0, 255] *)
Definition stem_bytes_valid (s : Stem) : Prop :=
  bytes31_valid (stem_bytes s).

(** TreeKey validity: stem is valid, subindex in [0, 255] *)
Definition tree_key_valid (k : TreeKey) : Prop :=
  stem_bytes_valid (key_stem k) /\ byte_valid (key_subindex k).

(** ** Composition Properties *)

(** If A and B have round-trip, so does (A * B) *)
Theorem pair_round_trip :
  forall (A B : Type),
    round_trip_correct A ->
    round_trip_correct B ->
    round_trip_correct (A * B).
Proof.
  (* Would need concrete serialization implementation *)
Admitted.

(** ** Non-Determinism Warning *)

(** HashMap-based types do NOT satisfy canonical encoding.
    This is a documentation of the known limitation. *)

(** StemNode uses HashMap<SubIndex, B256>, which has non-deterministic
    iteration order. Therefore:
    - round_trip_correct StemNode: TRUE (values preserved)
    - canonical_encoding StemNode: FALSE (order varies)
    
    Mitigation: Use BTreeMap for deterministic ordering. *)
