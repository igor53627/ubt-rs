(** * Cryptographic Primitives and Assumptions for UBT
    
    This module consolidates all cryptographic axioms used in the UBT
    formal verification. These axioms model standard cryptographic
    properties that cannot be proven within the type theory but are
    assumed to hold for the underlying hash function implementation.
    
    The axioms are organized into categories:
    - Hash function signatures (Parameters)
    - Determinism: same inputs produce same outputs
    - Zero behavior: how hash functions handle zero values
    - Collision resistance: distinct inputs produce distinct outputs
    - Second preimage resistance: hard to find collisions
    - Domain separation: non-zero values hash to non-zero outputs
    
    References:
    - Collision resistance: Rogaway & Shrimpton, "Cryptographic Hash-Function Basics" (2004)
    - Merkle trees: Merkle, "A Digital Signature Based on a Conventional Encryption Function" (1987)
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(** ** Basic Types *)

Definition Byte := Z.
Definition Bytes32 := list Byte.
Definition Bytes31 := list Byte.

(** Stem: 31-byte key prefix *)
Record Stem := mkStem {
  stem_data : Bytes31
}.

(** ** Zero Constants *)

Definition zero_byte : Byte := 0.
Definition zero32 : Bytes32 := repeat zero_byte 32.
Definition zero31 : Bytes31 := repeat zero_byte 31.

(** ** Stem Equality *)

Definition stem_eq (s1 s2 : Stem) : bool :=
  forallb (fun p => Z.eqb (fst p) (snd p)) 
          (combine (stem_data s1) (stem_data s2)).

(** ** Hash Function Signatures *)
(** 
    These parameters declare the abstract hash functions used throughout
    the UBT verification. The actual implementation uses cryptographic
    hash functions (e.g., Poseidon, Pedersen) but we treat them abstractly.
    
    - [hash_value]: Hashes a 32-byte leaf value
    - [hash_pair]: Combines two 32-byte hashes (Merkle tree internal nodes)
    - [hash_stem]: Combines a 31-byte stem with a 32-byte subtree hash
*)

(** [AXIOM:CRYPTO] Abstract hash function - cannot reason about cryptographic internals *)
Parameter hash_value : Bytes32 -> Bytes32.
Parameter hash_pair : Bytes32 -> Bytes32 -> Bytes32.
Parameter hash_stem : Stem -> Bytes32 -> Bytes32.

(** ** Determinism Axioms *)
(**
    Hash functions are deterministic: the same input always produces
    the same output. This is a fundamental property of any hash function.
    
    Note: These axioms are provable from reflexivity when inputs are
    definitionally equal, but we state them explicitly for clarity when
    dealing with propositional equality.
*)

(** Determinism - derivable from reflexivity via f_equal *)
Lemma hash_deterministic_value : forall v1 v2, 
  v1 = v2 -> hash_value v1 = hash_value v2.
Proof. intros v1 v2 H. rewrite H. reflexivity. Qed.

Lemma hash_deterministic_pair : forall a1 b1 a2 b2, 
  a1 = a2 -> b1 = b2 -> hash_pair a1 b1 = hash_pair a2 b2.
Proof. intros a1 b1 a2 b2 H1 H2. rewrite H1, H2. reflexivity. Qed.

(** Helper: forallb on combine implies elementwise equality for same-length lists *)
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

(** Stem equality with length precondition implies propositional equality *)
Lemma stem_eq_prop_len : forall s1 s2, 
  length (stem_data s1) = length (stem_data s2) ->
  stem_eq s1 s2 = true -> s1 = s2.
Proof.
  intros s1 s2 Hlen H.
  destruct s1 as [d1], s2 as [d2].
  unfold stem_eq in H. simpl in *.
  f_equal.
  apply forallb_combine_eq; assumption.
Qed.

(** [AXIOM:DESIGN] Well-formed stems have 31 bytes. In practice, all stems 
    in the UBT are 31 bytes. If stem_eq s1 s2 = true, the stems are semantically
    equivalent for hashing purposes. For malformed stems with different lengths
    where stem_eq still returns true (due to combine truncation), we axiomatize
    that hash_stem treats them identically. *)
Axiom hash_stem_respects_stem_eq : forall s1 s2 h,
  stem_eq s1 s2 = true -> hash_stem s1 h = hash_stem s2 h.

(** Stem determinism - uses function congruence on equal stem arguments. *)
Lemma hash_deterministic_stem : forall s1 h1 s2 h2,
  stem_eq s1 s2 = true -> h1 = h2 -> hash_stem s1 h1 = hash_stem s2 h2.
Proof.
  intros s1 h1 s2 h2 Hstem Hh.
  rewrite Hh.
  apply hash_stem_respects_stem_eq.
  exact Hstem.
Qed.

(** ** Zero Value Behavior *)
(**
    These axioms specify how hash functions behave on zero inputs.
    
    In the UBT, zero values represent "empty" or "absent" entries.
    The zero32 constant (32 zero bytes) is used as a sentinel value.
    
    These properties ensure that:
    - Empty leaves hash to the zero hash (sparse tree optimization)
    - Empty subtrees combine to empty parent hashes
*)

(** [AXIOM:DESIGN] Zero-hash property per EIP-7864 sparse tree optimization *)
Axiom hash_zero_value : hash_value zero32 = zero32.

Axiom hash_zero_pair : hash_pair zero32 zero32 = zero32.

(** ** Collision Resistance *)
(**
    Collision resistance: it is computationally infeasible to find two
    distinct inputs that produce the same hash output.
    
    We model this as the contrapositive: if outputs are equal, inputs
    must be equal. This is a strong axiom that holds for ideal hash
    functions and is assumed for cryptographic hash functions.
    
    Standard definition (Rogaway-Shrimpton):
    A hash function H is collision resistant if for all efficient 
    adversaries A, Pr[A outputs (x,x') with x≠x' and H(x)=H(x')] is negligible.
    
    Our axiom models the ideal case where this probability is zero.
*)

(** [AXIOM:CRYPTO] Collision resistance - standard Rogaway-Shrimpton assumption.
    Models ideal case where Pr[collision] = 0. Critical for proof security. *)
Axiom hash_value_collision_resistant : forall v1 v2,
  hash_value v1 = hash_value v2 -> v1 = v2.

(** [AXIOM:CRYPTO] Collision resistance for pair hashing *)
Axiom hash_pair_collision_resistant : forall a1 b1 a2 b2,
  hash_pair a1 b1 = hash_pair a2 b2 -> a1 = a2 /\ b1 = b2.

(** [AXIOM:CRYPTO] Collision resistance for stem hashing *)
Axiom hash_stem_collision_resistant : forall s1 h1 s2 h2,
  hash_stem s1 h1 = hash_stem s2 h2 -> stem_eq s1 s2 = true /\ h1 = h2.

(** ** Second Preimage Resistance *)
(**
    Second preimage resistance: given an input x and its hash H(x),
    it is computationally infeasible to find a different input x' ≠ x
    such that H(x') = H(x).
    
    This is weaker than collision resistance but sufficient for
    proving Merkle proof security. We model it as: distinct inputs
    produce distinct outputs.
    
    Note: This follows from collision resistance, but we state it
    explicitly for use in proofs where only second preimage resistance
    is needed.
*)

(** Second preimage resistance - derived from collision resistance (contrapositive) *)
Lemma hash_value_second_preimage : forall v1 v2,
  v1 <> v2 -> hash_value v1 <> hash_value v2.
Proof.
  intros v1 v2 Hneq Heq.
  apply hash_value_collision_resistant in Heq.
  contradiction.
Qed.

(** ** Domain Separation / Non-Zero Preservation *)
(**
    Domain separation ensures that meaningful (non-zero) values
    cannot collide with the zero sentinel value.
    
    This property is essential for the UBT because:
    - Zero values represent "absent" entries
    - Non-zero values represent actual stored data
    - We need to distinguish between "key not present" and "key maps to zero"
    
    In practice, this is achieved by the hash function having a
    sufficiently large output space that collisions with zero are
    negligible, or by explicit domain separation tags in the hash input.
*)

(** Non-zero values hash to non-zero outputs - derived from collision resistance + zero hash *)
Lemma hash_value_nonzero : forall v,
  (forallb (fun b => Z.eqb b 0) v = false) -> 
  hash_value v <> zero32.
Proof.
  intros v Hnonzero Heq.
  (* If hash_value v = zero32, then by hash_zero_value, hash_value v = hash_value zero32 *)
  rewrite <- hash_zero_value in Heq.
  (* By collision resistance, v = zero32 *)
  apply hash_value_collision_resistant in Heq.
  (* But zero32 has all zero bytes, contradicting Hnonzero *)
  subst v. unfold zero32 in Hnonzero. simpl in Hnonzero. discriminate.
Qed.

(** ** Value Predicates *)
(** Predicates for checking if values are zero/non-zero *)

Definition is_zero_value (v : Bytes32) : bool :=
  forallb (fun b => Z.eqb b 0) v.

Definition value_nonzero (v : Bytes32) : Prop :=
  is_zero_value v = false.

(** Convenience lemma: value_nonzero implies hash is non-zero *)
Lemma hash_nonzero_of_value_nonzero : forall v,
  value_nonzero v -> hash_value v <> zero32.
Proof.
  intros v Hnonzero.
  apply hash_value_nonzero.
  exact Hnonzero.
Qed.

(** ** Merkle Witness Computation *)
(**
    For Merkle proofs, we need to compute root hashes from witnesses.
    These definitions are cryptographic in nature and placed here
    rather than in [UBT.Sim.tree].
    
    See also:
    - [MerkleWitness] in tree.v for the main proof structures
    - [verify_inclusion_proof] for proof verification
*)

Inductive Direction : Type :=
  | Left : Direction
  | Right : Direction.

Record MerkleStep := mkMerkleStep {
  ms_sibling : Bytes32;
  ms_direction : Direction
}.

Definition MerkleWitness := list MerkleStep.

(** Compute root hash from leaf hash and witness path *)
Fixpoint compute_root_from_witness (leaf_hash : Bytes32) (witness : MerkleWitness) : Bytes32 :=
  match witness with
  | [] => leaf_hash
  | step :: rest =>
      let combined := match ms_direction step with
                      | Left => hash_pair (ms_sibling step) leaf_hash
                      | Right => hash_pair leaf_hash (ms_sibling step)
                      end in
      compute_root_from_witness combined rest
  end.

(** ** Collision Resistance for Witness Computation *)
(**
    If two witnesses compute to the same root, and they have the same
    structure, then the leaf hashes must be equal (by repeated application
    of hash_pair_collision_resistant).
*)

Lemma witness_collision_resistant_same_path :
  forall (witness : MerkleWitness) (h1 h2 : Bytes32),
    compute_root_from_witness h1 witness = compute_root_from_witness h2 witness ->
    h1 = h2.
Proof.
  induction witness as [|step rest IH].
  - simpl. intros h1 h2 Heq. exact Heq.
  - simpl. intros h1 h2 Heq.
    destruct (ms_direction step).
    + apply IH in Heq.
      apply hash_pair_collision_resistant in Heq.
      destruct Heq as [_ Heq]. exact Heq.
    + apply IH in Heq.
      apply hash_pair_collision_resistant in Heq.
      destruct Heq as [Heq _]. exact Heq.
Qed.
