(** OCaml Ctypes stubs for Rust FFI
    
    This module binds to the Rust FFI library using OCaml's Ctypes.
    
    Build requirements:
    - opam install ctypes ctypes-foreign
    - Rust library must be compiled: cd ffi/rust && cargo build --release
    
    Usage:
      open Ffi_stubs
      let hash = blake3_hash_32 input_bytes
*)

(* Note: This file requires the ctypes library.
   If ctypes is not installed, the ffi_bridge.ml placeholder implementations
   will be used instead. *)

#ifdef USE_CTYPES

open Ctypes
open Foreign

(** Path to the compiled Rust library *)
let lib_path = 
  if Sys.file_exists "ffi/rust/target/release/libubt_ffi.dylib" then
    "ffi/rust/target/release/libubt_ffi.dylib"
  else if Sys.file_exists "ffi/rust/target/release/libubt_ffi.so" then
    "ffi/rust/target/release/libubt_ffi.so"
  else if Sys.file_exists "../ffi/rust/target/release/libubt_ffi.dylib" then
    "../ffi/rust/target/release/libubt_ffi.dylib"
  else
    failwith "Cannot find libubt_ffi library. Run: cd ffi/rust && cargo build --release"

(** Load the Rust library *)
let lib = Dl.dlopen ~filename:lib_path ~flags:[Dl.RTLD_NOW]

(** BLAKE3 hash of 32 bytes *)
let rust_blake3_hash_32 =
  foreign ~from:lib "rust_blake3_hash_32"
    (ptr uint8_t @-> ptr uint8_t @-> returning void)

(** BLAKE3 hash of 64 bytes (left || right) *)
let rust_blake3_hash_64 =
  foreign ~from:lib "rust_blake3_hash_64"
    (ptr uint8_t @-> ptr uint8_t @-> ptr uint8_t @-> returning void)

(** BLAKE3 hash for stem nodes *)
let rust_blake3_hash_stem =
  foreign ~from:lib "rust_blake3_hash_stem"
    (ptr uint8_t @-> ptr uint8_t @-> ptr uint8_t @-> returning void)

(** SHA256 hash of 32 bytes *)
let rust_sha256_hash_32 =
  foreign ~from:lib "rust_sha256_hash_32"
    (ptr uint8_t @-> ptr uint8_t @-> returning void)

(** SHA256 hash of 64 bytes *)
let rust_sha256_hash_64 =
  foreign ~from:lib "rust_sha256_hash_64"
    (ptr uint8_t @-> ptr uint8_t @-> ptr uint8_t @-> returning void)

(** FFI version string *)
let rust_ubt_ffi_version =
  foreign ~from:lib "rust_ubt_ffi_version"
    (void @-> returning (ptr char))


(** {1 High-level OCaml wrappers} *)

(** Convert Bytes.t to Ctypes uint8_t array *)
let bytes_to_carray (b : bytes) : Unsigned.uint8 CArray.t =
  let len = Bytes.length b in
  let arr = CArray.make uint8_t len in
  for i = 0 to len - 1 do
    CArray.set arr i (Unsigned.UInt8.of_int (Bytes.get_uint8 b i))
  done;
  arr

(** Convert Ctypes uint8_t array to Bytes.t *)
let carray_to_bytes (arr : Unsigned.uint8 CArray.t) : bytes =
  let len = CArray.length arr in
  let b = Bytes.create len in
  for i = 0 to len - 1 do
    Bytes.set_uint8 b i (Unsigned.UInt8.to_int (CArray.get arr i))
  done;
  b

(** BLAKE3 hash 32 bytes -> 32 bytes (high-level wrapper) *)
let blake3_hash_32 (input : bytes) : bytes =
  assert (Bytes.length input = 32);
  let input_arr = bytes_to_carray input in
  let output_arr = CArray.make uint8_t 32 in
  rust_blake3_hash_32 (CArray.start input_arr) (CArray.start output_arr);
  carray_to_bytes output_arr

(** BLAKE3 hash 64 bytes -> 32 bytes (high-level wrapper) *)
let blake3_hash_64 (left : bytes) (right : bytes) : bytes =
  assert (Bytes.length left = 32);
  assert (Bytes.length right = 32);
  let left_arr = bytes_to_carray left in
  let right_arr = bytes_to_carray right in
  let output_arr = CArray.make uint8_t 32 in
  rust_blake3_hash_64 
    (CArray.start left_arr) 
    (CArray.start right_arr) 
    (CArray.start output_arr);
  carray_to_bytes output_arr

(** BLAKE3 hash stem node (high-level wrapper) *)
let blake3_hash_stem (stem : bytes) (subtree_root : bytes) : bytes =
  assert (Bytes.length stem = 31);
  assert (Bytes.length subtree_root = 32);
  let stem_arr = bytes_to_carray stem in
  let root_arr = bytes_to_carray subtree_root in
  let output_arr = CArray.make uint8_t 32 in
  rust_blake3_hash_stem
    (CArray.start stem_arr)
    (CArray.start root_arr)
    (CArray.start output_arr);
  carray_to_bytes output_arr

(** SHA256 hash 32 bytes -> 32 bytes (high-level wrapper) *)
let sha256_hash_32 (input : bytes) : bytes =
  assert (Bytes.length input = 32);
  let input_arr = bytes_to_carray input in
  let output_arr = CArray.make uint8_t 32 in
  rust_sha256_hash_32 (CArray.start input_arr) (CArray.start output_arr);
  carray_to_bytes output_arr

(** Get FFI library version *)
let ffi_version () : string =
  let ptr = rust_ubt_ffi_version () in
  Ctypes.coerce (ptr char) string ptr

#else

(** Placeholder implementations when Ctypes is not available *)

let blake3_hash_32 (_input : bytes) : bytes =
  failwith "Ctypes not available. Install with: opam install ctypes ctypes-foreign"

let blake3_hash_64 (_left : bytes) (_right : bytes) : bytes =
  failwith "Ctypes not available"

let blake3_hash_stem (_stem : bytes) (_subtree_root : bytes) : bytes =
  failwith "Ctypes not available"

let sha256_hash_32 (_input : bytes) : bytes =
  failwith "Ctypes not available"

let ffi_version () : string = "ctypes-not-available"

#endif
