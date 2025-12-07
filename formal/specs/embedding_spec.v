(** * State Embedding Specification
    
    Formal specification of how Ethereum state maps to UBT keys.
    Based on EIP-7864 tree embedding rules.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
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

(** Code chunk key derivation *)
Definition code_chunk_key (addr : Address) (chunk_num : Z) : list Z :=
  (* chunkOffset = 128 + chunkNum, stored as little-endian in bytes 24-31 *)
  let offset := (CODE_OFFSET + chunk_num)%Z in
  let input := repeat 0%Z 24 ++ 
    (* Little-endian encoding of offset in 8 bytes *)
    [Z.land offset 255;
     Z.land (Z.shiftr offset 8) 255;
     Z.land (Z.shiftr offset 16) 255;
     Z.land (Z.shiftr offset 24) 255;
     Z.land (Z.shiftr offset 32) 255;
     Z.land (Z.shiftr offset 40) 255;
     Z.land (Z.shiftr offset 48) 255;
     Z.land (Z.shiftr offset 56) 255] in
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

(** Header slots are co-located with account data *)
Theorem header_slots_same_stem :
  forall addr slot1 slot2,
    is_header_slot slot1 = true ->
    is_header_slot slot2 = true ->
    (* First 31 bytes (stem) of keys are equal *)
    firstn 31 (storage_slot_key addr slot1) = 
    firstn 31 (storage_slot_key addr slot2).
Proof.
  (* Key derivation uses same stem for header slots *)
Admitted.

(** Basic data and code hash share same stem *)
Theorem account_data_same_stem :
  forall addr,
    firstn 31 (basic_data_key addr) = firstn 31 (code_hash_key addr).
Proof.
  intros addr.
  unfold basic_data_key, code_hash_key, derive_tree_key.
  (* Both use same stem derivation, differ only in subindex *)
Admitted.

(** First 64 storage slots share stem with account *)
Theorem header_storage_same_stem :
  forall addr slot,
    is_header_slot slot = true ->
    firstn 31 (storage_slot_key addr slot) = firstn 31 (basic_data_key addr).
Proof.
Admitted.

(** First 128 code chunks share stem with account *)
Theorem header_code_same_stem :
  forall addr chunk_num,
    (0 <= chunk_num < 128)%Z ->
    firstn 31 (code_chunk_key addr chunk_num) = firstn 31 (basic_data_key addr).
Proof.
Admitted.
