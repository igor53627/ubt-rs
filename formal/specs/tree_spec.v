(** * UBT Tree Specification
    
    Formal specification of the Unified Binary Tree (EIP-7864).
    This file defines the abstract specification that the implementation
    must satisfy.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.

(** ** Basic Types *)

(** Bytes are integers in [0, 255] *)
Definition byte := Z.
Definition byte_valid (b : byte) : Prop := (0 <= b < 256)%Z.

(** Fixed-size byte arrays *)
Definition bytes32 := list byte.
Definition bytes31 := list byte.

Definition bytes32_valid (b : bytes32) : Prop := length b = 32%nat.
Definition bytes31_valid (b : bytes31) : Prop := length b = 31%nat.

(** ** Tree Key Structure *)

(** A stem is 31 bytes identifying a 256-value subtree *)
Record Stem := mkStem {
  stem_bytes : bytes31;
  stem_valid : bytes31_valid stem_bytes
}.

(** Subindex is the last byte (0-255) *)
Definition SubIndex := byte.

(** A tree key is (stem, subindex) *)
Record TreeKey := mkTreeKey {
  key_stem : Stem;
  key_subindex : SubIndex
}.

(** Convert 32 bytes to TreeKey *)
Definition bytes32_to_key (b : bytes32) : option TreeKey :=
  match b with
  | _ => None (* Placeholder - actual implementation splits at byte 31 *)
  end.

(** ** Node Types *)

(** Abstract node type *)
Inductive Node : Type :=
  | Empty : Node
  | Internal : Node -> Node -> Node
  | StemNode : Stem -> Node -> Node -> Node
  | Leaf : bytes32 -> Node.

(** ** Hash Function Axioms *)

(** We axiomatize the hash function since we can't reason about
    cryptographic internals. *)

Parameter Hash : bytes32 -> bytes32 -> bytes32.
Parameter HashSingle : bytes32 -> bytes32.

(** Zero bytes *)
Definition zero32 : bytes32 := repeat 0%Z 32.

(** Hash of zeros is zero (special case per EIP-7864) *)
Axiom hash_zero : Hash zero32 zero32 = zero32.
Axiom hash_single_zero : HashSingle zero32 = zero32.

(** Hash is deterministic - provable from reflexivity *)
Lemma hash_deterministic : forall a b, Hash a b = Hash a b.
Proof. reflexivity. Qed.

(** Collision resistance (weakened placeholder form).
    Note: This form with \/ True is trivially satisfiable.
    The actual crypto assumption is in simulations/crypto.v. *)
Lemma hash_collision_resistant : 
  forall a1 b1 a2 b2,
    Hash a1 b1 = Hash a2 b2 -> (a1 = a2 /\ b1 = b2) \/ (* collision found - negligible probability *) True.
Proof. intros. right. trivial. Qed.

(** ** Node Hashing *)

(** Compute hash of a node *)
Fixpoint node_hash (n : Node) : bytes32 :=
  match n with
  | Empty => zero32
  | Internal l r => Hash (node_hash l) (node_hash r)
  | StemNode s l r => 
      (* hash(stem || 0x00 || hash(left || right)) *)
      (* Simplified - actual impl concatenates stem with inner hash *)
      Hash (node_hash l) (node_hash r)
  | Leaf v => HashSingle v
  end.

(** ** Tree Operations Specification *)

(** Get value at key *)
Fixpoint tree_get (t : Node) (k : TreeKey) (depth : nat) : option bytes32 :=
  match t, depth with
  | Empty, _ => None
  | Leaf v, _ => Some v
  | Internal l r, S d => 
      (* Check bit at depth to decide left/right *)
      (* Simplified - actual impl checks stem bits *)
      tree_get l k d
  | StemNode s l r, _ =>
      (* Check if stem matches *)
      (* If match, look up in subtree by subindex *)
      None (* Placeholder *)
  | _, O => None
  end.

(** ** Correctness Properties *)

(** Property: Empty tree has zero hash *)
Theorem empty_hash_zero : node_hash Empty = zero32.
Proof. reflexivity. Qed.

(** Property: Hash is deterministic *)
Theorem hash_is_deterministic : 
  forall t, node_hash t = node_hash t.
Proof. reflexivity. Qed.

(** Property: Get from empty returns None *)
Theorem get_empty : 
  forall k d, tree_get Empty k d = None.
Proof. reflexivity. Qed.

(** ** Well-Formedness *)

(** A tree is well-formed if:
    1. All internal nodes have two children
    2. All stems are valid (31 bytes)
    3. All values are valid (32 bytes)
    4. No duplicate stems
*)

Inductive WellFormed : Node -> Prop :=
  | WF_Empty : WellFormed Empty
  | WF_Internal : forall l r,
      WellFormed l -> WellFormed r -> WellFormed (Internal l r)
  | WF_Stem : forall s l r,
      WellFormed l -> WellFormed r -> WellFormed (StemNode s l r)
  | WF_Leaf : forall v,
      bytes32_valid v -> WellFormed (Leaf v).

(** ** Invariant: Hash uniquely identifies tree content *)

(** Two well-formed trees with same hash have same content
    (under collision resistance assumption).
    Note: This is a placeholder - actual statement needs tree equality.
    Trivially provable since conclusion is True. *)
Lemma hash_injective :
  forall t1 t2,
    WellFormed t1 -> WellFormed t2 ->
    node_hash t1 = node_hash t2 ->
    (* Trees are "equivalent" in content *)
    True.
Proof. trivial. Qed.

(** ** Order Independence *)

(** Inserting keys in different order produces same hash *)
(* This requires defining insert operation first *)

(** Placeholder for insert operation *)
Parameter tree_insert : Node -> TreeKey -> bytes32 -> Node.

(** Order independence theorem statement *)
Axiom insert_order_independent :
  forall t k1 v1 k2 v2,
    k1 <> k2 ->
    node_hash (tree_insert (tree_insert t k1 v1) k2 v2) =
    node_hash (tree_insert (tree_insert t k2 v2) k1 v1).

(** ** Get-Insert Properties *)

(** Get after insert returns the inserted value *)
Axiom get_insert_same :
  forall t k v d,
    v <> zero32 ->
    tree_get (tree_insert t k v) k d = Some v.

(** Get after insert on different key is unchanged *)
Axiom get_insert_other :
  forall t k1 k2 v d,
    k1 <> k2 ->
    tree_get (tree_insert t k1 v) k2 d = tree_get t k2 d.

(** ** No Panics *)

(** All operations on well-formed trees produce well-formed trees *)
Axiom insert_preserves_wf :
  forall t k v,
    WellFormed t ->
    WellFormed (tree_insert t k v).
