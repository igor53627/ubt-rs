(** * Type Links for UBT
    
    This module defines Link instances connecting:
    - Simulation types (SimTree, Stem, TreeKey, etc.) in simulations/tree.v
    - Translated Rust types (UnifiedBinaryTree, Stem, TreeKey) in src/tree.v
    
    The linking approach follows rocq-of-rust conventions:
    - Link typeclass provides Φ (Rust type) and φ (encoding function)
    - OfTy.t witnesses Rocq type ↔ Rust type correspondence
    - OfValue.t witnesses Rocq value ↔ Rust value correspondence
*)

Require Import RocqOfRust.RocqOfRust.
Require Import RocqOfRust.links.M.
Require Import RocqOfRust.simulations.M.

Require Import Stdlib.Lists.List.
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

(** ** SubIndexMap linking (list of (SubIndex * Value) pairs) *)

Module SubIndexMapLink.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "std::collections::hash::map::HashMap") []
      [Ty.path "u8"; Bytes32Link.Rust_ty; Ty.path "std::hash::random::RandomState"].
  
  Fixpoint subindexmap_to_value (m : SubIndexMap) : Value.t :=
    Value.StructRecord "std::collections::hash::map::HashMap" [] 
      [Ty.path "u8"; Bytes32Link.Rust_ty; Ty.path "std::hash::random::RandomState"]
      [].
  
  Global Instance IsLink : Link SubIndexMap := {
    Φ := Rust_ty;
    φ m := subindexmap_to_value m;
  }.
End SubIndexMapLink.

(** ** StemMap linking *)

Module StemMapLink.
  Definition Rust_ty : Ty.t := 
    Ty.apply (Ty.path "std::collections::hash::map::HashMap") []
      [StemLink.Rust_ty; Ty.path "ubt::node::StemNode"; 
       Ty.path "std::hash::random::RandomState"].
  
  Global Instance IsLink : Link StemMap := {
    Φ := Rust_ty;
    φ m := Value.StructRecord "std::collections::hash::map::HashMap" []
             [StemLink.Rust_ty; Ty.path "ubt::node::StemNode"; 
              Ty.path "std::hash::random::RandomState"]
             [];
  }.
End StemMapLink.

(** ** SimTree linking to UnifiedBinaryTree<H> *)

Module SimTreeLink.
  Definition Rust_ty (H : Ty.t) : Ty.t := 
    Ty.apply (Ty.path "ubt::tree::UnifiedBinaryTree") [] [H].
  
  Global Instance IsLink (H : Ty.t) : Link SimTree := {
    Φ := Rust_ty H;
    φ t := Value.StructRecord "ubt::tree::UnifiedBinaryTree" [] [H]
             [("root", Value.StructTuple "ubt::node::Node::Empty" [] [] []);
              ("hasher", Value.StructTuple "unit" [] [] []);
              ("stems", φ (st_stems t))];
  }.
End SimTreeLink.

(** ** Link hints for smpl tactic *)

#[export] Hint Resolve ByteLink.of_ty : of_ty.
#[export] Hint Resolve Bytes32Link.of_ty : of_ty.
#[export] Hint Resolve StemLink.of_ty : of_ty.
#[export] Hint Resolve SubIndexLink.of_ty : of_ty.
#[export] Hint Resolve TreeKeyLink.of_ty : of_ty.
#[export] Hint Resolve ValueLink.of_ty : of_ty.
