(** * Correctness Proofs
    
    Main correctness proofs for the UBT implementation.
    These proofs show that the simulation layer (idiomatic Rocq)
    satisfies the EIP-7864 specification.
    
    The verification follows rocq-of-rust's recommended workflow:
    
    1. TRANSLATION: Auto-generated Rocq from Rust (in src/)
    2. LINKING: Add type information to translated code
    3. SIMULATION: Write idiomatic Rocq (in simulations/)
    4. PROOFS: Show simulation ≈ translation, simulation satisfies spec
    
    Currently proven at the simulation level:
    - Empty tree properties
    - Get/Insert correctness
    - Delete correctness  
    - Hash determinism
    - Stem co-location
    - Well-formedness preservation
    
    Pending (require linking layer):
    - Full simulation-translation equivalence
    - No-panic guarantees via monadic analysis
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(* Import the simulation layer *)
Require Import UBT.Sim.tree.

(** ** Core Tree Correctness Theorems *)

(**
   Theorem 1: Empty tree has zero hash
   
   The root hash of an empty UBT is 32 zero bytes.
   This is directly proven in the simulation layer.
*)
Theorem empty_tree_zero_hash :
  sim_node_hash SimEmpty = zero32.
Proof.
  exact empty_tree_hash_zero.
Qed.

(**
   Theorem 2: Hash determinism
   
   The same tree always produces the same root hash.
   This follows from functional purity.
*)
Theorem hash_deterministic :
  forall n : SimNode, sim_node_hash n = sim_node_hash n.
Proof.
  exact hash_deterministic_node.
Qed.

(**
   Theorem 3: Get from empty tree
   
   Getting any key from an empty tree returns None.
*)
Theorem get_from_empty :
  forall k : TreeKey, sim_tree_get empty_tree k = None.
Proof.
  exact get_empty.
Qed.

(**
   Theorem 4: Get-Insert correctness
   
   After inserting (k, v), getting k returns v (if v ≠ all zeros).
   get(insert(T, k, v), k) = Some(v)
*)
Theorem get_insert_same_key :
  forall t k v,
    value_nonzero v ->
    sim_tree_get (sim_tree_insert t k v) k = Some v.
Proof.
  exact get_insert_same.
Qed.

(**
   Theorem 5: Get-Insert-Other correctness (different stems)
   
   Inserting at k1 doesn't affect get at k2 when stems differ.
*)
Theorem get_insert_different_stem :
  forall t k1 k2 v,
    stem_eq (tk_stem k1) (tk_stem k2) = false ->
    sim_tree_get (sim_tree_insert t k1 v) k2 = sim_tree_get t k2.
Proof.
  exact get_insert_other_stem.
Qed.

(**
   Theorem 6: Get-Insert-Other correctness (same stem, different subindex)
   
   Inserting at k1 doesn't affect get at k2 when they share stem
   but have different subindices.
*)
Theorem get_insert_different_subindex :
  forall t k1 k2 v,
    stem_eq (tk_stem k1) (tk_stem k2) = true ->
    tk_subindex k1 <> tk_subindex k2 ->
    sim_tree_get (sim_tree_insert t k1 v) k2 = sim_tree_get t k2.
Proof.
  exact get_insert_other_subindex.
Qed.

(**
   Theorem 7: Delete correctness
   
   After deleting k, getting k returns None.
   get(delete(T, k), k) = None
*)
Theorem get_after_delete :
  forall t k,
    sim_tree_get (sim_tree_delete t k) k = None.
Proof.
  exact get_delete.
Qed.

(**
   Theorem 8: Stem co-location
   
   Keys with same stem are stored in the same subtree.
   This is proven by showing they access the same StemNode.
*)
Theorem keys_share_stem_node :
  forall t k1 k2,
    stem_eq (tk_stem k1) (tk_stem k2) = true ->
    forall v, 
      exists submap,
        stems_get (st_stems (sim_tree_insert t k1 v)) (tk_stem k1) = Some submap /\
        stems_get (st_stems (sim_tree_insert t k1 v)) (tk_stem k2) = Some submap.
Proof.
  exact stem_colocation.
Qed.

(**
   Theorem 9: Well-formedness preservation
   
   Insertion preserves tree well-formedness.
*)
Theorem insertion_preserves_wellformedness :
  forall t k v,
    wf_tree t -> wf_value v -> wf_stem (tk_stem k) ->
    wf_tree (sim_tree_insert t k v).
Proof.
  exact insert_preserves_wf.
Qed.

(** ** Order Independence (Partial) *)

(**
   Theorem 10: Order independence for different stems
   
   When inserting keys with different stems, the order doesn't matter
   for the final tree state (extensional equality).
   
   Note: This is partially proven (admits in some cases).
*)
Theorem order_independence_different_stems :
  forall t k1 v1 k2 v2,
    stem_eq (tk_stem k1) (tk_stem k2) = false ->
    tree_eq 
      (sim_tree_insert (sim_tree_insert t k1 v1) k2 v2)
      (sim_tree_insert (sim_tree_insert t k2 v2) k1 v1).
Proof.
  exact insert_order_independent_stems.
Qed.

(** ** Axiomatized Properties *)

(**
   These properties hold by the hash function axioms.
   They cannot be proven without access to hash internals.
*)

Theorem hash_zero_is_zero :
  hash_value zero32 = zero32.
Proof.
  exact hash_zero_value.
Qed.

Theorem hash_pair_zero_is_zero :
  hash_pair zero32 zero32 = zero32.
Proof.
  exact hash_zero_pair.
Qed.

(** ** Future Work: Translation Linking *)

(**
   The following theorems require linking the rocq-of-rust translation
   (in src/) with the simulation layer (in simulations/).
   
   This linking proves that the Rust implementation behaves identically
   to the simulation, allowing the simulation proofs to transfer.
   
   Pending theorems:
   - Translation-simulation equivalence for insert
   - Translation-simulation equivalence for get
   - Translation-simulation equivalence for delete
   - No-panic guarantee via monadic termination analysis
   - Merkle proof verification
   - Witness size bounds
   
   These require:
   1. Building the RocqOfRust library (needs coq-hammer 9.x)
   2. Creating linking modules between src/*.v and simulations/*.v
   3. Proving behavioral equivalence via refinement proofs
*)

(** Placeholder for translation-simulation linking *)
Module Type TranslationSimulationLink.
  (** 
     When the translation is linked, we will prove:
     
     rust_insert ≈ sim_tree_insert
     rust_get ≈ sim_tree_get  
     rust_delete ≈ sim_tree_delete
     rust_hash ≈ sim_node_hash
     
     Where ≈ denotes behavioral equivalence modulo
     the monadic structure of the translation.
  *)
  Parameter translation_simulation_equiv : Prop.
End TranslationSimulationLink.
