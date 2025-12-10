(** * State Embedding Specification
    
    Formal specification of how Ethereum state maps to UBT keys.
    Based on EIP-7864 tree embedding rules.
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** ** Constants *)

Definition BASIC_DATA_LEAF_KEY : Z := 0.
Definition CODE_HASH_LEAF_KEY : Z := 1.
Definition HEADER_STORAGE_OFFSET : Z := 64.
Definition CODE_OFFSET : Z := 128.
Definition STEM_SUBTREE_WIDTH : Z := 256.

(** Main storage offset = 2^248 *)
(** Represented as first byte = 1 in 32-byte key *)

(** ** Types *)

Definition Address := list Z. (* 20 bytes *)
Definition address_valid (a : Address) : Prop := length a = 20%nat.

Definition StorageSlot := list Z. (* 32 bytes *)
Definition slot_valid (s : StorageSlot) : Prop := length s = 32%nat.

(** ** Key Derivation *)

(** SHA256 hash (axiomatized) *)
Parameter SHA256 : list Z -> list Z.

(** 12 zero bytes prefix *)
Definition zero_prefix : list Z := repeat 0%Z 12.

(** Key derivation function per go-ethereum:
    key = SHA256(0^12 || address || inputKey[0:31])
    key[31] = inputKey[31]
*)
Definition derive_tree_key (addr : Address) (input_key : list Z) : list Z :=
  let hash_input := zero_prefix ++ addr ++ (firstn 31 input_key) in
  let hash := SHA256 hash_input in
  (firstn 31 hash) ++ [nth 31 input_key 0%Z].

(** ** Account Data Keys *)

(** Basic data key (nonce, balance, code_size) *)
Definition basic_data_key (addr : Address) : list Z :=
  let input := repeat 0%Z 31 ++ [BASIC_DATA_LEAF_KEY] in
  derive_tree_key addr input.

(** Code hash key *)
Definition code_hash_key (addr : Address) : list Z :=
  let input := repeat 0%Z 31 ++ [CODE_HASH_LEAF_KEY] in
  derive_tree_key addr input.

(** ** Storage Slot Keys *)

(** Check if slot is in header storage (first 64 slots) *)
Definition is_header_slot (slot : StorageSlot) : bool :=
  match slot with
  | s => 
    (* Check if first 31 bytes are zero and last byte < 64 *)
    let first31 := firstn 31 s in
    let last := nth 31 s 0%Z in
    (forallb (fun b => Z.eqb b 0) first31) && (last <? 64)%Z
  end.

(** Storage slot key derivation *)
Definition storage_slot_key (addr : Address) (slot : StorageSlot) : list Z :=
  if is_header_slot slot then
    (* Header slot: subindex = 64 + slot[31] *)
    let input := repeat 0%Z 31 ++ [(HEADER_STORAGE_OFFSET + nth 31 slot 0)%Z] in
    derive_tree_key addr input
  else
    (* Main storage: set first byte to 1 (= 2^248 offset) *)
    let input := [1%Z] ++ (firstn 30 (skipn 1 slot)) ++ [nth 31 slot 0%Z] in
    derive_tree_key addr input.

(** ** Code Chunk Keys *)

(** Code chunk key derivation - corrected per EIP-7864 *)
Definition code_chunk_key (addr : Address) (chunk_num : Z) : list Z :=
  let pos := (CODE_OFFSET + chunk_num)%Z in
  if (pos <? STEM_SUBTREE_WIDTH)%Z then
    (* First 128 chunks: same stem as account, subindex = pos *)
    let input := repeat 0%Z 31 ++ [pos] in
    derive_tree_key addr input
  else
    (* Later chunks: encode stem_index into first 31 bytes *)
    let stem_index := (pos / STEM_SUBTREE_WIDTH)%Z in
    let subindex := (pos mod STEM_SUBTREE_WIDTH)%Z in
    (* encode stem_index as big-endian in bytes 23-30 *)
    let input := repeat 0%Z 23 ++ 
      [Z.land (Z.shiftr stem_index 56) 255;
       Z.land (Z.shiftr stem_index 48) 255;
       Z.land (Z.shiftr stem_index 40) 255;
       Z.land (Z.shiftr stem_index 32) 255;
       Z.land (Z.shiftr stem_index 24) 255;
       Z.land (Z.shiftr stem_index 16) 255;
       Z.land (Z.shiftr stem_index 8) 255;
       Z.land stem_index 255;
       subindex] in
    derive_tree_key addr input.

(** ** Basic Data Layout *)

(** 
   Basic data leaf format (32 bytes):
   - Byte 0: version
   - Bytes 1-4: reserved
   - Bytes 5-7: code_size (big-endian, 3 bytes)
   - Bytes 8-15: nonce (big-endian, 8 bytes)
   - Bytes 16-31: balance (big-endian, 16 bytes)
*)

Record BasicData := mkBasicData {
  bd_version : Z;
  bd_code_size : Z;
  bd_nonce : Z;
  bd_balance : Z
}.

(** Encode basic data to 32 bytes *)
Definition encode_basic_data (bd : BasicData) : list Z :=
  [bd_version bd] ++                           (* byte 0 *)
  repeat 0%Z 4 ++                               (* bytes 1-4: reserved *)
  (* code_size: 3 bytes big-endian *)
  [Z.land (Z.shiftr (bd_code_size bd) 16) 255;
   Z.land (Z.shiftr (bd_code_size bd) 8) 255;
   Z.land (bd_code_size bd) 255] ++
  (* nonce: 8 bytes big-endian *)
  [Z.land (Z.shiftr (bd_nonce bd) 56) 255;
   Z.land (Z.shiftr (bd_nonce bd) 48) 255;
   Z.land (Z.shiftr (bd_nonce bd) 40) 255;
   Z.land (Z.shiftr (bd_nonce bd) 32) 255;
   Z.land (Z.shiftr (bd_nonce bd) 24) 255;
   Z.land (Z.shiftr (bd_nonce bd) 16) 255;
   Z.land (Z.shiftr (bd_nonce bd) 8) 255;
   Z.land (bd_nonce bd) 255] ++
  (* balance: 16 bytes big-endian - simplified *)
  repeat 0%Z 16.  (* Placeholder for full balance encoding *)

(** ** Properties *)

(** SHA256 determinism - same input gives same output (trivially provable) *)
Lemma SHA256_deterministic : forall x, SHA256 x = SHA256 x.
Proof. reflexivity. Qed.

(** Helper: firstn 31 of (repeat 0 31 ++ [x]) = repeat 0 31 *)
Lemma firstn_31_repeat_0_app : forall x,
  firstn 31 (repeat 0%Z 31 ++ [x]) = repeat 0%Z 31.
Proof.
  intros x.
  rewrite firstn_app.
  rewrite repeat_length.
  replace (31 - 31)%nat with 0%nat by lia.
  rewrite firstn_all2 by (rewrite repeat_length; lia).
  rewrite firstn_O. rewrite app_nil_r.
  reflexivity.
Qed.

(** Helper: firstn n (l ++ _) = l when length l = n *)
Lemma firstn_app_exact : forall {A : Type} (n : nat) (l1 l2 : list A),
  length l1 = n ->
  firstn n (l1 ++ l2) = l1.
Proof.
  intros A n l1 l2 Hlen.
  rewrite firstn_app.
  rewrite Hlen.
  replace (n - n)%nat with 0%nat by lia.
  rewrite firstn_all2 by lia.
  rewrite firstn_O. rewrite app_nil_r.
  reflexivity.
Qed.

(** Helper: length of SHA256 output is 32 bytes (axiom) *)
Axiom SHA256_length : forall x, length (SHA256 x) = 32%nat.

(** Helper: length of firstn is bounded *)
Lemma firstn_length_le' : forall {A : Type} (n : nat) (l : list A),
  (n <= length l)%nat ->
  length (firstn n l) = n.
Proof.
  intros. apply firstn_length_le. assumption.
Qed.

(** Helper: firstn n (firstn n l ++ _) = firstn n l when n <= length l *)
Lemma firstn_firstn_app : forall {A : Type} (n : nat) (l rest : list A),
  (n <= length l)%nat ->
  firstn n (firstn n l ++ rest) = firstn n l.
Proof.
  intros A n l rest Hlen.
  rewrite firstn_app.
  rewrite firstn_length_le by assumption.
  replace (n - n)%nat with 0%nat by lia.
  rewrite firstn_firstn.
  replace (Init.Nat.min n n) with n by lia.
  rewrite firstn_O. rewrite app_nil_r.
  reflexivity.
Qed.

(** Header slots are co-located with account data *)
Theorem header_slots_same_stem :
  forall addr slot1 slot2,
    is_header_slot slot1 = true ->
    is_header_slot slot2 = true ->
    (* First 31 bytes (stem) of keys are equal *)
    firstn 31 (storage_slot_key addr slot1) = 
    firstn 31 (storage_slot_key addr slot2).
Proof.
  intros addr slot1 slot2 H1 H2.
  unfold storage_slot_key.
  rewrite H1, H2.
  unfold derive_tree_key.
  (* The stem is firstn 31 of the full key.
     Key = firstn 31 (SHA256(0^12 || addr || firstn 31 input)) ++ [subindex]
     So stem = firstn 31 (SHA256(0^12 || addr || firstn 31 input))
     
     For header slots, input = 0^31 ++ [64 + slot[31]]
     So firstn 31 input = 0^31 for all header slots.
     Therefore the hash input is the same: SHA256(0^12 || addr || 0^31)
     And the stems are equal. *)
  rewrite !firstn_31_repeat_0_app.
  rewrite !firstn_firstn_app by (rewrite SHA256_length; lia).
  reflexivity.
Qed.

(** Basic data and code hash share same stem *)
Theorem account_data_same_stem :
  forall addr,
    firstn 31 (basic_data_key addr) = firstn 31 (code_hash_key addr).
Proof.
  intros addr.
  unfold basic_data_key, code_hash_key, derive_tree_key.
  (* Both use same stem derivation: SHA256(0^12 || addr || 0^31)
     Only the subindex differs (0 vs 1), but that's byte 31. *)
  (* First rewrite the inner firstn 31 of (repeat 0 31 ++ [x]) to repeat 0 31 *)
  rewrite (firstn_31_repeat_0_app BASIC_DATA_LEAF_KEY).
  rewrite (firstn_31_repeat_0_app CODE_HASH_LEAF_KEY).
  (* Now both SHA256 inputs are the same *)
  rewrite !firstn_firstn_app by (rewrite SHA256_length; lia).
  reflexivity.
Qed.

(** First 64 storage slots share stem with account *)
Theorem header_storage_same_stem :
  forall addr slot,
    is_header_slot slot = true ->
    firstn 31 (storage_slot_key addr slot) = firstn 31 (basic_data_key addr).
Proof.
  intros addr slot Hheader.
  unfold storage_slot_key, basic_data_key, derive_tree_key.
  rewrite Hheader.
  (* Both use same hash input for stem: SHA256(0^12 || addr || 0^31) *)
  rewrite !firstn_31_repeat_0_app.
  rewrite !firstn_firstn_app by (rewrite SHA256_length; lia).
  reflexivity.
Qed.

(** First 128 code chunks share stem with account.
    
    With the corrected EIP-7864 implementation:
    - For chunk_num in [0, 128), pos = 128 + chunk_num is in [128, 256)
    - Since pos < 256 = STEM_SUBTREE_WIDTH, we use input = repeat 0 31 ++ [pos]
    - Therefore firstn 31 input = repeat 0 31, same as basic_data_key
    - The SHA256 hash input is identical, so stems are equal. *)
Theorem header_code_same_stem :
  forall addr chunk_num,
    (0 <= chunk_num < 128)%Z ->
    firstn 31 (code_chunk_key addr chunk_num) = firstn 31 (basic_data_key addr).
Proof.
  intros addr chunk_num Hrange.
  unfold code_chunk_key, basic_data_key, derive_tree_key.
  (* pos = 128 + chunk_num, with chunk_num in [0, 128), so pos in [128, 256) *)
  (* Since pos < 256 = STEM_SUBTREE_WIDTH, the condition (pos <? 256) is true *)
  assert (Hpos : (CODE_OFFSET + chunk_num <? STEM_SUBTREE_WIDTH)%Z = true).
  { unfold CODE_OFFSET, STEM_SUBTREE_WIDTH. lia. }
  rewrite Hpos.
  (* Now both use input with firstn 31 input = repeat 0 31 *)
  rewrite !firstn_31_repeat_0_app.
  rewrite !firstn_firstn_app by (rewrite SHA256_length; lia).
  reflexivity.
Qed.
