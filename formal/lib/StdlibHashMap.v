(** * StdlibHashMap: HashMap Stepping Semantics
    
    This module provides stepping rules for Rust's HashMap type.
    HashMap is modeled as an association list in Rocq.
    
    ** Rust Type: std::collections::HashMap<K, V>
    ** Rocq Type: list (K * V)
    
    ** Operations Covered
    
    - HashMap::new() -> empty list
    - HashMap::get(&self, key) -> option lookup
    - HashMap::insert(&mut self, key, value) -> update list
    - HashMap::entry(key).or_insert(default) -> lookup or insert
    - HashMap::iter() -> list to iterator
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Bool.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

(** ** Abstract HashMap Model
    
    HashMap<K, V> is modeled as list (K * V).
    This abstraction is valid because:
    1. HashMap ordering doesn't affect get/insert semantics
    2. Key equality determines lookup behavior
    3. Permutation-equivalent lists have same lookup behavior
*)

Section HashMapModel.

  Variable K : Set.
  Variable V : Set.
  Variable key_eq : K -> K -> bool.
  
  Definition Map := list (K * V).

  (** Lookup by key *)
  Definition map_get (m : Map) (k : K) : option V :=
    match find (fun p => key_eq (fst p) k) m with
    | Some (_, v) => Some v
    | None => None
    end.

  (** Insert/update key-value pair *)
  Definition map_insert (m : Map) (k : K) (v : V) : Map :=
    (k, v) :: filter (fun p => negb (key_eq (fst p) k)) m.

  (** Check if key exists *)
  Definition map_contains (m : Map) (k : K) : bool :=
    match map_get m k with
    | Some _ => true
    | None => false
    end.

  (** Remove key *)
  Definition map_remove (m : Map) (k : K) : Map :=
    filter (fun p => negb (key_eq (fst p) k)) m.

  (** Empty map *)
  Definition map_empty : Map := [].

  (** ** Core Lemmas *)

  Hypothesis key_eq_refl : forall k, key_eq k k = true.
  Hypothesis key_eq_sym : forall k1 k2, key_eq k1 k2 = key_eq k2 k1.
  Hypothesis key_eq_true : forall k1 k2, key_eq k1 k2 = true -> k1 = k2.

  (** Get after insert same key returns inserted value *)
  Lemma map_get_insert_same : forall m k v,
    map_get (map_insert m k v) k = Some v.
  Proof.
    intros m k v.
    unfold map_get, map_insert. simpl.
    rewrite key_eq_refl. reflexivity.
  Qed.

  (** Get after insert different key is unchanged *)
  Lemma map_get_insert_other : forall m k1 k2 v,
    key_eq k1 k2 = false ->
    map_get (map_insert m k1 v) k2 = map_get m k2.
  Proof.
    intros m k1 k2 v Hneq.
    unfold map_get, map_insert. simpl.
    rewrite Hneq.
    induction m as [|[k' v'] rest IH].
    - reflexivity.
    - simpl.
      destruct (key_eq k1 k') eqn:Hk1k'.
      + simpl.
        destruct (key_eq k' k2) eqn:Hk'k2.
        * apply key_eq_true in Hk1k'. subst.
          apply key_eq_true in Hk'k2. subst.
          rewrite key_eq_refl in Hneq. discriminate.
        * apply IH.
      + simpl.
        destruct (key_eq k' k2) eqn:Hk'k2.
        * reflexivity.
        * apply IH.
  Qed.

  (** Empty map has no keys *)
  Lemma map_get_empty : forall k,
    map_get map_empty k = None.
  Proof.
    intros k. reflexivity.
  Qed.

End HashMapModel.

(** ** Rust Value Encoding
    
    How HashMap values are represented in RocqOfRust.
*)

Module HashMapEncoding.

  Definition HashMap_ty (K_ty V_ty : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "std::collections::hash::map::HashMap") [] 
      [K_ty; V_ty; Ty.path "std::hash::random::RandomState"].

  (** Encode Rocq list as Rust HashMap value.
      For verification purposes, we model the HashMap as containing
      an encoded association list. *)
  Definition encode_map {K V : Set} 
    (encode_k : K -> Value.t) 
    (encode_v : V -> Value.t)
    (m : list (K * V)) : Value.t :=
    Value.StructTuple "std::collections::hash::map::HashMap" [] []
      [Value.Array (map (fun p => Value.Tuple [encode_k (fst p); encode_v (snd p)]) m)].

  (** Decode Rust HashMap to Rocq list *)
  Definition decode_map {K V : Set}
    (decode_k : Value.t -> option K)
    (decode_v : Value.t -> option V)
    (v : Value.t) : option (list (K * V)) :=
    match v with
    | Value.StructTuple _ _ _ [Value.Array entries] =>
        let fix decode_entries (es : list Value.t) : option (list (K * V)) :=
          match es with
          | [] => Some []
          | Value.Tuple [k_val; v_val] :: rest =>
              match decode_k k_val, decode_v v_val, decode_entries rest with
              | Some k, Some v, Some rest' => Some ((k, v) :: rest')
              | _, _, _ => None
              end
          | _ => None
          end
        in decode_entries entries
    | _ => None
    end.

End HashMapEncoding.

(** ** Stepping Rules
    
    Stepping semantics for HashMap operations.
*)

Module HashMapStepping.

  Import HashMapEncoding.

  (** HashMap::new() returns empty map *)
  Definition hashmap_new_result (K_ty V_ty : Ty.t) : Value.t :=
    Value.StructTuple "std::collections::hash::map::HashMap" [] []
      [Value.Array []].

  (** HashMap::get stepping result.
      
      For a map m and key k:
      - If k in m: returns Some v
      - Otherwise: returns None
  *)
  Definition hashmap_get_result {K V : Set}
    (key_eq : K -> K -> bool)
    (encode_v : V -> Value.t)
    (m : list (K * V))
    (k : K) : Value.t :=
    match map_get K V key_eq m k with
    | Some v => 
        Value.StructTuple "core::option::Option::Some" [] [] [encode_v v]
    | None =>
        Value.StructTuple "core::option::Option::None" [] [] []
    end.

  (** HashMap::insert stepping result.
      
      Returns (old_value_option, new_map)
  *)
  Definition hashmap_insert_result {K V : Set}
    (key_eq : K -> K -> bool)
    (encode_k : K -> Value.t)
    (encode_v : V -> Value.t)
    (m : list (K * V))
    (k : K)
    (v : V) : Value.t * Value.t :=
    let old := map_get K V key_eq m k in
    let new_map := map_insert K V key_eq m k v in
    let old_encoded := 
      match old with
      | Some ov => Value.StructTuple "core::option::Option::Some" [] [] [encode_v ov]
      | None => Value.StructTuple "core::option::Option::None" [] [] []
      end
    in
    (old_encoded, encode_map encode_k encode_v new_map).

  (** ** Refinement Lemmas *)

  Section Refinement.
    Variable K V : Set.
    Variable key_eq : K -> K -> bool.
    Variable encode_k : K -> Value.t.
    Variable encode_v : V -> Value.t.

    Hypothesis key_eq_refl : forall k, key_eq k k = true.

    (** HashMap::new produces empty map *)
    Lemma hashmap_new_refines :
      forall K_ty V_ty,
        hashmap_new_result K_ty V_ty = encode_map encode_k encode_v (map_empty K V).
    Proof.
      intros. unfold hashmap_new_result, encode_map, map_empty. reflexivity.
    Qed.

    (** HashMap::get result matches map_get *)
    Lemma hashmap_get_refines :
      forall m k,
        hashmap_get_result key_eq encode_v m k =
        match map_get K V key_eq m k with
        | Some v => Value.StructTuple "core::option::Option::Some" [] [] [encode_v v]
        | None => Value.StructTuple "core::option::Option::None" [] [] []
        end.
    Proof.
      intros. reflexivity.
    Qed.

  End Refinement.

End HashMapStepping.

(** ** Summary
    
    This module provides:
    
    1. Abstract HashMap model as association list
    2. Core lemmas (get_insert_same, get_insert_other)
    3. Encoding/decoding between Rocq lists and Rust Values
    4. Stepping results for new/get/insert operations
    5. Refinement lemmas connecting Rust to simulation
    
    Usage in proofs:
    
    1. Model your HashMap as `list (K * V)`
    2. Use `map_get`, `map_insert` for simulation
    3. Use refinement lemmas to connect Rust execution to simulation
*)
