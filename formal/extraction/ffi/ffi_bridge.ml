(** FFI Bridge: OCaml Extracted Code <-> Rust UBT
    
    This module provides an interface between the formally verified 
    OCaml extracted code and the Rust UBT implementation.
    
    Architecture:
    - OCaml extracted code provides verified tree operations  
    - Rust provides efficient cryptographic primitives (BLAKE3/SHA256)
    - Communication via C-compatible FFI types
*)

open Extracted

(** {1 FFI Type Conversions} *)

(** Convert OCaml bytes list to a C-compatible byte array (Bytes.t) *)
let bytes_of_list (lst : byte0 list) : bytes =
  let len = List.length lst in
  let b = Bytes.create len in
  List.iteri (fun i v -> Bytes.set_uint8 b i (v land 0xFF)) lst;
  b

(** Convert C-compatible byte array to OCaml bytes list *)
let list_of_bytes (b : bytes) : byte0 list =
  List.init (Bytes.length b) (fun i -> Bytes.get_uint8 b i)

(** Convert stem (31 bytes) to Bytes.t *)
let stem_to_bytes (s : stem) : bytes =
  let result = bytes_of_list s in
  assert (Bytes.length result = 31);
  result

(** Convert Bytes.t to stem *)
let bytes_to_stem (b : bytes) : stem =
  assert (Bytes.length b = 31);
  list_of_bytes b

(** Convert value (32 bytes) to Bytes.t *)
let value_to_bytes (v : value) : bytes =
  bytes_of_list v

(** Convert Bytes.t to value (padded to 32 bytes) *)
let bytes_to_value (b : bytes) : value =
  let lst = list_of_bytes b in
  let len = List.length lst in
  if len >= 32 then List.filteri (fun i _ -> i < 32) lst
  else lst @ List.init (32 - len) (fun _ -> 0)

(** Convert treeKey to a 32-byte buffer *)
let tree_key_to_bytes (k : treeKey) : bytes =
  let stem_bytes = stem_to_bytes k.tk_stem in
  let result = Bytes.create 32 in
  Bytes.blit stem_bytes 0 result 0 31;
  Bytes.set_uint8 result 31 (k.tk_subindex land 0xFF);
  result

(** Convert 32-byte buffer to treeKey *)
let bytes_to_tree_key (b : bytes) : treeKey =
  assert (Bytes.length b = 32);
  let stem_bytes = Bytes.sub b 0 31 in
  { tk_stem = bytes_to_stem stem_bytes;
    tk_subindex = Bytes.get_uint8 b 31 }


(** {1 External Hash Function Stubs}
    
    These functions are designed to be replaced with actual FFI calls
    to the Rust implementation. Currently they use placeholder implementations.
*)

(** BLAKE3 hash of 32 bytes -> 32 bytes
    In production: calls rust_blake3_hash via C FFI *)
let blake3_hash_32 (input : bytes) : bytes =
  (* PLACEHOLDER: Replace with actual FFI call *)
  let result = Bytes.create 32 in
  for i = 0 to min (Bytes.length input - 1) 31 do
    Bytes.set_uint8 result i (Bytes.get_uint8 input i)
  done;
  result

(** BLAKE3 hash of 64 bytes -> 32 bytes (for internal nodes)
    In production: calls rust_blake3_hash_pair via C FFI *)
let blake3_hash_64 (left : bytes) (right : bytes) : bytes =
  (* PLACEHOLDER: Replace with actual FFI call *)
  let combined = Bytes.create 64 in
  Bytes.blit left 0 combined 0 (min (Bytes.length left) 32);
  Bytes.blit right 0 combined 32 (min (Bytes.length right) 32);
  blake3_hash_32 (Bytes.sub combined 0 32)

(** BLAKE3 hash for stem node: hash(stem || 0x00 || subtree_root)
    In production: calls rust_blake3_hash_stem via C FFI *)
let blake3_hash_stem (stem_bytes : bytes) (subtree_root : bytes) : bytes =
  (* PLACEHOLDER: Replace with actual FFI call *)
  let combined = Bytes.create 64 in
  Bytes.blit stem_bytes 0 combined 0 (min (Bytes.length stem_bytes) 31);
  Bytes.set_uint8 combined 31 0;
  Bytes.blit subtree_root 0 combined 32 (min (Bytes.length subtree_root) 32);
  blake3_hash_32 (Bytes.sub combined 0 32)


(** {1 Hash Function Implementations Using FFI}
    
    These replace the placeholder implementations in extracted.ml
*)

(** Hash a 32-byte value using BLAKE3 *)
let hash_value_ffi (v : value) : bytes0 =
  let input = value_to_bytes v in
  let result = blake3_hash_32 input in
  list_of_bytes result

(** Hash two 32-byte values (for internal nodes) *)
let hash_pair_ffi (a : bytes0) (b : bytes0) : bytes0 =
  let left = value_to_bytes a in
  let right = value_to_bytes b in
  let result = blake3_hash_64 left right in
  list_of_bytes result

(** Hash a stem node *)
let hash_stem_ffi (s : stem) (h : bytes0) : bytes0 =
  let stem_bytes = stem_to_bytes s in
  let subtree = value_to_bytes h in
  let result = blake3_hash_stem stem_bytes subtree in
  list_of_bytes result


(** {1 Tree Operations with FFI-backed Hashing}
    
    These wrap the extracted tree operations with real hash functions.
*)

(** Compute hash of a simNode using FFI-backed hash functions *)
let rec compute_node_hash (node : simNode) : bytes0 =
  match node with
  | SimEmpty -> zero32
  | SimInternal (l, r) -> 
      hash_pair_ffi (compute_node_hash l) (compute_node_hash r)
  | SimStem (s, _m) -> 
      hash_stem_ffi s zero32
  | SimLeaf v -> 
      hash_value_ffi v


(** {1 Test Utilities} *)

(** Print bytes as hex string *)
let hex_of_bytes (b : bytes) : string =
  let len = Bytes.length b in
  let result = Buffer.create (len * 2) in
  for i = 0 to len - 1 do
    Buffer.add_string result (Printf.sprintf "%02x" (Bytes.get_uint8 b i))
  done;
  Buffer.contents result

(** Parse hex string to bytes *)
let bytes_of_hex (s : string) : bytes =
  let len = String.length s / 2 in
  let result = Bytes.create len in
  for i = 0 to len - 1 do
    let byte = int_of_string ("0x" ^ String.sub s (i * 2) 2) in
    Bytes.set_uint8 result i byte
  done;
  result

(** Pretty-print a tree key *)
let string_of_tree_key (k : treeKey) : string =
  Printf.sprintf "TreeKey { stem: 0x%s, subindex: %d }"
    (hex_of_bytes (stem_to_bytes k.tk_stem))
    k.tk_subindex


(** {1 FFI Entry Points}
    
    These are the main functions exposed for Rust interop.
    Each returns C-compatible types for easier FFI marshalling.
*)

type ffi_tree = simTree

(** Create an empty tree *)
let ffi_empty_tree () : ffi_tree = empty_tree

(** Get a value from the tree. Returns null (empty bytes) if not found. *)
let ffi_get (tree : ffi_tree) (key_bytes : bytes) : bytes =
  let key = bytes_to_tree_key key_bytes in
  match sim_tree_get tree key with
  | Some v -> value_to_bytes v
  | None -> Bytes.empty

(** Insert a key-value pair. Returns the new tree. *)
let ffi_insert (tree : ffi_tree) (key_bytes : bytes) (value_bytes : bytes) : ffi_tree =
  let key = bytes_to_tree_key key_bytes in
  let value = bytes_to_value value_bytes in
  sim_tree_insert tree key value

(** Delete a key. Returns the new tree. *)
let ffi_delete (tree : ffi_tree) (key_bytes : bytes) : ffi_tree =
  let key = bytes_to_tree_key key_bytes in
  sim_tree_delete tree key

(** Check if a value exists (non-zero) *)
let ffi_contains (tree : ffi_tree) (key_bytes : bytes) : bool =
  let key = bytes_to_tree_key key_bytes in
  match sim_tree_get tree key with
  | Some v -> not (is_zero_value v)
  | None -> false
