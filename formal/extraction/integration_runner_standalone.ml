(** Standalone OCaml Integration Test Runner
    
    This is a standalone version that implements the UBT simulation
    directly in OCaml for testing the integration infrastructure.
    It mirrors the Rocq extracted code but doesn't depend on extraction.
    
    Build:
      cd formal/extraction && ocamlfind ocamlopt -package str -linkpkg integration_runner_standalone.ml -o integration_runner
    
    Or without ocamlfind:
      cd formal/extraction && ocamlopt str.cmxa integration_runner_standalone.ml -o integration_runner
    
    Run:
      ./integration_runner < test_data.txt > ocaml_results.txt
*)

(** {1 UBT Types - mirrors Extracted module} *)

type bytes31 = int list
type bytes0 = int list
type stem = bytes31

type treeKey = {
  tk_stem: stem;
  tk_subindex: int;
}

module StemMap = Map.Make(struct
  type t = stem
  let compare = compare
end)

module IntMap = Map.Make(Int)

type subIndexMap = bytes0 IntMap.t
type simTree = subIndexMap StemMap.t

let empty_tree : simTree = StemMap.empty

let zero32 : bytes0 = List.init 32 (fun _ -> 0)

let stem_eq (s1 : stem) (s2 : stem) : bool = s1 = s2

let is_zero_value (v : bytes0) : bool =
  List.for_all (fun x -> x = 0) v

let sim_tree_get (tree : simTree) (key : treeKey) : bytes0 option =
  match StemMap.find_opt key.tk_stem tree with
  | None -> None
  | Some submap ->
      match IntMap.find_opt key.tk_subindex submap with
      | None -> None
      | Some v -> if is_zero_value v then None else Some v

let sim_tree_insert (tree : simTree) (key : treeKey) (value : bytes0) : simTree =
  let submap = match StemMap.find_opt key.tk_stem tree with
    | None -> IntMap.empty
    | Some m -> m
  in
  let submap' = IntMap.add key.tk_subindex value submap in
  StemMap.add key.tk_stem submap' tree

let sim_tree_delete (tree : simTree) (key : treeKey) : simTree =
  match StemMap.find_opt key.tk_stem tree with
  | None -> tree
  | Some submap ->
      let submap' = IntMap.add key.tk_subindex zero32 submap in
      StemMap.add key.tk_stem submap' tree

(** {1 Integration Test Runner} *)

let pad_to_length lst n fill =
  let len = List.length lst in
  if len >= n then
    List.filteri (fun i _ -> i < n) lst
  else
    lst @ (List.init (n - len) (fun _ -> fill))

let make_bytes32 (values : int list) : bytes0 =
  pad_to_length values 32 0

let make_bytes31 (values : int list) : bytes31 =
  pad_to_length values 31 0

let make_stem (bytes : int list) : stem =
  make_bytes31 bytes

let make_key (stem_bytes : int list) (subindex : int) : treeKey =
  { tk_stem = make_stem stem_bytes; tk_subindex = subindex }

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
      |> List.map int_of_string

let format_bytes (bytes : int list) : string =
  let bytes32 = pad_to_length bytes 32 0 in
  String.concat "," (List.map string_of_int bytes32)

let format_result (result : bytes0 option) : string =
  match result with
  | None -> "None"
  | Some bytes -> Printf.sprintf "Some([%s])" (format_bytes bytes)

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
                  | _ -> ())
             | _ -> ())
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
