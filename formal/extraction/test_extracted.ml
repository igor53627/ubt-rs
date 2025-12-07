(** OCaml Test Harness for Extracted UBT Code
    
    This file tests the extracted Rocq code to verify basic functionality.
    
    Build: After running 'make extract', compile with:
      cd extraction && ocamlfind ocamlopt extracted.ml test_extracted.ml -o test_ubt
    
    Or simpler:
      cd extraction && ocamlopt extracted.ml test_extracted.ml -o test_ubt
*)

open Extracted

(** Helper: Create a bytes32 (list of 32 int values) *)
let make_bytes32 (values : int list) : bytes0 =
  let rec pad lst n =
    if n <= 0 then List.rev lst
    else match List.rev lst with
      | [] -> pad [0] (n - 1)
      | _ -> pad (0 :: (List.rev lst)) (n - 1)
  in
  if List.length values >= 32 then
    List.map (fun x -> x) (List.filteri (fun i _ -> i < 32) values)
  else
    values @ (List.init (32 - List.length values) (fun _ -> 0))

(** Helper: Create a bytes31 (list of 31 int values) *)
let make_bytes31 (values : int list) : bytes31 =
  if List.length values >= 31 then
    List.map (fun x -> x) (List.filteri (fun i _ -> i < 31) values)
  else
    values @ (List.init (31 - List.length values) (fun _ -> 0))

(** Helper: Create a stem from bytes *)
let make_stem (bytes : int list) : stem =
  make_bytes31 bytes

(** Helper: Create a tree key *)
let make_key (stem_bytes : int list) (subindex : int) : treeKey =
  { tk_stem = make_stem stem_bytes; tk_subindex = subindex }

(** Helper: Print test result *)
let print_result (name : string) (passed : bool) =
  let status = if passed then "PASS" else "FAIL" in
  Printf.printf "[%s] %s\n" status name

(** Test 1: Empty tree returns None for any key *)
let test_empty_tree () =
  let tree = empty_tree in
  let key = make_key [1; 2; 3] 5 in
  let result = sim_tree_get tree key in
  let passed = result = None in
  print_result "Empty tree get returns None" passed;
  passed

(** Test 2: Insert then get returns the value *)
let test_insert_get () =
  let tree = empty_tree in
  let key = make_key [1; 2; 3; 4; 5] 10 in
  let value = make_bytes32 [42; 43; 44; 45] in
  let tree' = sim_tree_insert tree key value in
  let result = sim_tree_get tree' key in
  let passed = result = Some value in
  print_result "Insert then get same key" passed;
  passed

(** Test 3: Get different key returns None *)
let test_get_different_key () =
  let tree = empty_tree in
  let key1 = make_key [1; 2; 3] 10 in
  let key2 = make_key [4; 5; 6] 20 in
  let value = make_bytes32 [100; 101; 102] in
  let tree' = sim_tree_insert tree key1 value in
  let result = sim_tree_get tree' key2 in
  let passed = result = None in
  print_result "Get different stem returns None" passed;
  passed

(** Test 4: Same stem, different subindex *)
let test_same_stem_different_subindex () =
  let tree = empty_tree in
  let key1 = make_key [1; 2; 3] 10 in
  let key2 = make_key [1; 2; 3] 20 in
  let value = make_bytes32 [100; 101; 102] in
  let tree' = sim_tree_insert tree key1 value in
  let result = sim_tree_get tree' key2 in
  let passed = result = None in
  print_result "Same stem, different subindex returns None" passed;
  passed

(** Test 5: Multiple inserts with same stem *)
let test_multiple_inserts_same_stem () =
  let tree = empty_tree in
  let key1 = make_key [1; 2; 3] 10 in
  let key2 = make_key [1; 2; 3] 20 in
  let value1 = make_bytes32 [100; 101; 102] in
  let value2 = make_bytes32 [200; 201; 202] in
  let tree' = sim_tree_insert tree key1 value1 in
  let tree'' = sim_tree_insert tree' key2 value2 in
  let result1 = sim_tree_get tree'' key1 in
  let result2 = sim_tree_get tree'' key2 in
  let passed = result1 = Some value1 && result2 = Some value2 in
  print_result "Multiple inserts same stem" passed;
  passed

(** Test 6: Delete removes value *)
let test_delete () =
  let tree = empty_tree in
  let key = make_key [1; 2; 3] 10 in
  let value = make_bytes32 [42; 43; 44] in
  let tree' = sim_tree_insert tree key value in
  let tree'' = sim_tree_delete tree' key in
  let result = sim_tree_get tree'' key in
  let passed = result = None in
  print_result "Delete removes value" passed;
  passed

(** Test 7: Stem equality works correctly *)
let test_stem_equality () =
  let stem1 = make_stem [1; 2; 3] in
  let stem2 = make_stem [1; 2; 3] in
  let stem3 = make_stem [1; 2; 4] in
  let eq12 = stem_eq stem1 stem2 in
  let eq13 = stem_eq stem1 stem3 in
  let passed = eq12 = true && eq13 = false in
  print_result "Stem equality" passed;
  passed

(** Test 8: is_zero_value works correctly *)
let test_is_zero_value () =
  let zero = zero32 in
  let nonzero = make_bytes32 [1] in
  let is_zero_zero = is_zero_value zero in
  let is_zero_nonzero = is_zero_value nonzero in
  let passed = is_zero_zero = true && is_zero_nonzero = false in
  print_result "is_zero_value predicate" passed;
  passed

(** Test 9: Merkle witness computation *)
let test_merkle_witness () =
  let leaf_hash = make_bytes32 [1; 2; 3] in
  let result = compute_root_from_witness leaf_hash [] in
  let passed = result = leaf_hash in
  print_result "Empty Merkle witness returns leaf" passed;
  passed

(** Test 10: Insert preserves other values *)
let test_insert_preserves_others () =
  let tree = empty_tree in
  let key1 = make_key [10; 20; 30] 1 in
  let key2 = make_key [40; 50; 60] 2 in
  let key3 = make_key [70; 80; 90] 3 in
  let value1 = make_bytes32 [111] in
  let value2 = make_bytes32 [222] in
  let value3 = make_bytes32 [255; 254; 253] in
  let tree' = sim_tree_insert tree key1 value1 in
  let tree'' = sim_tree_insert tree' key2 value2 in
  let tree''' = sim_tree_insert tree'' key3 value3 in
  let r1 = sim_tree_get tree''' key1 in
  let r2 = sim_tree_get tree''' key2 in
  let r3 = sim_tree_get tree''' key3 in
  let passed = r1 = Some value1 && r2 = Some value2 && r3 = Some value3 in
  print_result "Insert preserves other values" passed;
  passed

(** Main test runner *)
let () =
  Printf.printf "=== UBT Extracted Code Tests ===\n\n";
  
  let tests = [
    test_empty_tree;
    test_insert_get;
    test_get_different_key;
    test_same_stem_different_subindex;
    test_multiple_inserts_same_stem;
    test_delete;
    test_stem_equality;
    test_is_zero_value;
    test_merkle_witness;
    test_insert_preserves_others;
  ] in
  
  let results = List.map (fun test -> test ()) tests in
  let passed = List.filter (fun x -> x) results |> List.length in
  let total = List.length results in
  
  Printf.printf "\n=== Results: %d/%d tests passed ===\n" passed total;
  
  if passed = total then
    Printf.printf "All tests passed!\n"
  else
    Printf.printf "Some tests failed.\n";
  
  exit (if passed = total then 0 else 1)
