(** OCaml Integration Test Runner
    
    Reads test data file and runs operations on extracted UBT code.
    Results are output in a format comparable to Rust output.
    
    Build:
      cd formal/extraction && ocamlfind ocamlopt extracted.ml integration_runner.ml -o integration_runner
    
    Run:
      ./integration_runner < test_data.txt > ocaml_results.txt
*)

open Extracted

(** Helper: Pad or truncate a list to exactly n elements *)
let pad_to_length lst n fill =
  let len = List.length lst in
  if len >= n then
    List.filteri (fun i _ -> i < n) lst
  else
    lst @ (List.init (n - len) (fun _ -> fill))

(** Helper: Create a bytes32 (list of 32 int values) *)
let make_bytes32 (values : int list) : bytes0 =
  pad_to_length values 32 0

(** Helper: Create a bytes31 (list of 31 int values) *)
let make_bytes31 (values : int list) : bytes31 =
  pad_to_length values 31 0

(** Helper: Create a stem from bytes *)
let make_stem (bytes : int list) : stem =
  make_bytes31 bytes

(** Helper: Create a tree key *)
let make_key (stem_bytes : int list) (subindex : int) : treeKey =
  { tk_stem = make_stem stem_bytes; tk_subindex = subindex }

(** Parse a bytes list from string like "[1,2,3]" *)
let parse_bytes (s : string) : int list =
  let s = String.trim s in
  if s = "[]" then []
  else
    let inner = 
      if String.length s >= 2 && s.[0] = '[' && s.[String.length s - 1] = ']' then
        String.sub s 1 (String.length s - 2)
      else s
    in
    if String.trim inner = "" then []
    else
      String.split_on_char ',' inner
      |> List.map String.trim
      |> List.filter (fun x -> x <> "")
      |> List.filter_map (fun s ->
           match int_of_string_opt s with
           | Some n -> Some n
           | None ->
               Printf.eprintf "[WARN] parse_bytes: invalid integer '%s'\n" s;
               None)

(** Format bytes list back to string *)
let format_bytes (bytes : int list) : string =
  let bytes32 = pad_to_length bytes 32 0 in
  String.concat "," (List.map string_of_int bytes32)

(** Format result *)
let format_result (result : bytes0 option) : string =
  match result with
  | None -> "None"
  | Some bytes -> Printf.sprintf "Some([%s])" (format_bytes bytes)

(** Test case structure *)
type operation =
  | Insert of int list * int * int list
  | Delete of int list * int

type query = {
  stem: int list;
  subindex: int;
}

type test_case = {
  name: string;
  mutable operations: operation list;
  mutable queries: query list;
}

(** Run a single test case *)
let run_test_case (test : test_case) : (string * bytes0 option) list =
  let tree = ref empty_tree in
  
  List.iter (fun op ->
    match op with
    | Insert (stem, subindex, value) ->
        let key = make_key stem subindex in
        let val_ = make_bytes32 value in
        tree := sim_tree_insert !tree key val_
    | Delete (stem, subindex) ->
        let key = make_key stem subindex in
        tree := sim_tree_delete !tree key
  ) test.operations;
  
  List.map (fun q ->
    let key = make_key q.stem q.subindex in
    let result = sim_tree_get !tree key in
    let query_id = Printf.sprintf "stem=[%s],subidx=%d"
      (String.concat "," (List.map string_of_int q.stem))
      q.subindex
    in
    (query_id, result)
  ) test.queries

(** Parse test data from stdin *)
let parse_test_data () : test_case list =
  let tests = ref [] in
  let current_test = ref None in
  
  try
    while true do
      let line = input_line stdin in
      let line = String.trim line in
      
      if String.length line = 0 || line.[0] = '#' then
        ()
      else if String.length line >= 5 && String.sub line 0 5 = "TEST " then begin
        (match !current_test with
         | Some t -> tests := t :: !tests
         | None -> ());
        let name = String.sub line 5 (String.length line - 5) in
        current_test := Some { name; operations = []; queries = [] }
      end
      else if String.length line >= 10 && String.sub line 0 10 = "OP INSERT " then begin
        match !current_test with
        | Some t ->
            let rest = String.sub line 10 (String.length line - 10) in
            let parts = Str.split (Str.regexp "\\] ") rest in
            (match parts with
             | stem_str :: idx_val_str :: [] ->
                 let stem = parse_bytes (stem_str ^ "]") in
                 let idx_val = Str.split (Str.regexp " \\[") idx_val_str in
                 (match idx_val with
                  | idx_str :: val_str :: [] ->
                      let subindex = int_of_string (String.trim idx_str) in
                      let value = parse_bytes ("[" ^ val_str) in
                      t.operations <- t.operations @ [Insert (stem, subindex, value)]
                  | _ ->
                      Printf.eprintf "[WARN] OP INSERT: failed to parse idx/value from '%s'\n" rest)
             | _ ->
                 Printf.eprintf "[WARN] OP INSERT: failed to parse stem from '%s'\n" rest)
        | None -> ()
      end
      else if String.length line >= 10 && String.sub line 0 10 = "OP DELETE " then begin
        match !current_test with
        | Some t ->
            let rest = String.sub line 10 (String.length line - 10) in
            let parts = Str.split (Str.regexp "\\] ") rest in
            (match parts with
             | stem_str :: idx_str :: [] ->
                 let stem = parse_bytes (stem_str ^ "]") in
                 let subindex = int_of_string (String.trim idx_str) in
                 t.operations <- t.operations @ [Delete (stem, subindex)]
             | _ -> ())
        | None -> ()
      end
      else if String.length line >= 6 && String.sub line 0 6 = "QUERY " then begin
        match !current_test with
        | Some t ->
            let rest = String.sub line 6 (String.length line - 6) in
            let parts = Str.split (Str.regexp "\\] ") rest in
            (match parts with
             | stem_str :: idx_str :: [] ->
                 let stem = parse_bytes (stem_str ^ "]") in
                 let subindex = int_of_string (String.trim idx_str) in
                 t.queries <- t.queries @ [{ stem; subindex }]
             | _ -> ())
        | None -> ()
      end
      else
        ()
    done;
    []
  with End_of_file ->
    (match !current_test with
     | Some t -> tests := t :: !tests
     | None -> ());
    List.rev !tests

(** Main entry point *)
let () =
  Printf.printf "# UBT OCaml Test Results\n\n";
  
  let tests = parse_test_data () in
  
  List.iter (fun test ->
    Printf.printf "TEST %s\n" test.name;
    let results = run_test_case test in
    List.iter (fun (query_id, result) ->
      Printf.printf "RESULT %s = %s\n" query_id (format_result result)
    ) results;
    Printf.printf "\n"
  ) tests
