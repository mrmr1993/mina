(** Gate sequence comparison between OCaml and nori circuit compilations.

    Compares gate JSON files dumped via [DUMP_PCS_GATES] on both sides.
    Each JSON file contains an array of gate objects with a "type" field.

    Usage:
      gate_comparison.compare ~reference_dir ~candidate_dir

    Reports: exact match, first divergence point, gate count delta by type. *)

open Core_kernel

(** Extract the ordered list of gate types from a gate JSON file.
    The JSON format is: [ {"type": "Generic", "wires": [...], "coeffs": [...]}, ... ] *)
let gate_types_of_json_file (path : string) : string list =
  let json = Yojson.Safe.from_file path in
  match json with
  | `List gates ->
      List.map gates ~f:(fun gate ->
          match gate with
          | `Assoc fields -> (
              match List.Assoc.find fields ~equal:String.equal "type" with
              | Some (`String ty) ->
                  ty
              | _ ->
                  failwithf "gate_types_of_json_file: missing 'type' in %s" path
                    () )
          | _ ->
              failwithf "gate_types_of_json_file: gate is not an object in %s"
                path () )
  | _ ->
      failwithf "gate_types_of_json_file: expected array in %s" path ()

(** Summary of gate types: type name -> count *)
let gate_summary (gates : string list) : (string * int) list =
  let counts = Hashtbl.create (module String) in
  List.iter gates ~f:(fun ty ->
      Hashtbl.update counts ty ~f:(function None -> 1 | Some n -> n + 1) ) ;
  Hashtbl.to_alist counts
  |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)

(** Find the first index where two gate lists diverge. *)
let first_divergence (a : string list) (b : string list) :
    (int * string option * string option) option =
  let rec go i la lb =
    match (la, lb) with
    | [], [] ->
        None
    | [], hb :: _ ->
        Some (i, None, Some hb)
    | ha :: _, [] ->
        Some (i, Some ha, None)
    | ha :: ta, hb :: tb ->
        if String.equal ha hb then go (i + 1) ta tb
        else Some (i, Some ha, Some hb)
  in
  go 0 a b

type comparison_result =
  { file : string
  ; reference_count : int
  ; candidate_count : int
  ; match_ : bool
  ; first_divergence : (int * string option * string option) option
  ; delta_by_type : (string * int) list
  }

(** Compare two gate JSON files. *)
let compare_files ~(reference_path : string) ~(candidate_path : string)
    ~(name : string) : comparison_result =
  let ref_gates = gate_types_of_json_file reference_path in
  let cand_gates = gate_types_of_json_file candidate_path in
  let ref_summary = gate_summary ref_gates in
  let cand_summary = gate_summary cand_gates in
  (* Compute delta: candidate - reference for each gate type *)
  let all_types =
    List.dedup_and_sort ~compare:String.compare
      (List.map ref_summary ~f:fst @ List.map cand_summary ~f:fst)
  in
  let delta_by_type =
    List.filter_map all_types ~f:(fun ty ->
        let r =
          List.Assoc.find ref_summary ~equal:String.equal ty
          |> Option.value ~default:0
        in
        let c =
          List.Assoc.find cand_summary ~equal:String.equal ty
          |> Option.value ~default:0
        in
        let d = c - r in
        if d <> 0 then Some (ty, d) else None )
  in
  { file = name
  ; reference_count = List.length ref_gates
  ; candidate_count = List.length cand_gates
  ; match_ = List.equal String.equal ref_gates cand_gates
  ; first_divergence = first_divergence ref_gates cand_gates
  ; delta_by_type
  }

(** Print a comparison result. *)
let print_result (r : comparison_result) =
  let status = if r.match_ then "EXACT MATCH" else "DIVERGES" in
  printf "  %-30s %s  (ref=%d, cand=%d, delta=%+d)\n" r.file status
    r.reference_count r.candidate_count
    (r.candidate_count - r.reference_count) ;
  if not r.match_ then (
    ( match r.first_divergence with
    | Some (idx, ref_gate, cand_gate) ->
        let ref_s = Option.value ref_gate ~default:"<end>" in
        let cand_s = Option.value cand_gate ~default:"<end>" in
        printf "    first divergence at gate %d: ref=%s, cand=%s\n" idx ref_s
          cand_s
    | None ->
        () ) ;
    if not (List.is_empty r.delta_by_type) then (
      printf "    delta by type:\n" ;
      List.iter r.delta_by_type ~f:(fun (ty, d) ->
          printf "      %-20s %+d\n" ty d ) ) )

(** List JSON files in a directory, sorted by name. *)
let list_json_files (dir : string) : string list =
  Stdlib.Sys.readdir dir |> Array.to_list
  |> List.filter ~f:(fun f -> String.is_suffix f ~suffix:".json")
  |> List.sort ~compare:String.compare

(** Compare all matching JSON files between two directories. *)
let compare_dirs ~(reference_dir : string) ~(candidate_dir : string) : unit =
  let ref_files = list_json_files reference_dir in
  let cand_files = list_json_files candidate_dir in
  printf "Gate Comparison: %s vs %s\n" reference_dir candidate_dir ;
  printf "  Reference files: %d\n" (List.length ref_files) ;
  printf "  Candidate files: %d\n\n" (List.length cand_files) ;
  (* Match files by name *)
  let ref_set = Set.of_list (module String) ref_files in
  let cand_set = Set.of_list (module String) cand_files in
  let common = Set.inter ref_set cand_set |> Set.to_list in
  let ref_only = Set.diff ref_set cand_set |> Set.to_list in
  let cand_only = Set.diff cand_set ref_set |> Set.to_list in
  let n_match = ref 0 in
  let n_diverge = ref 0 in
  List.iter common ~f:(fun file ->
      let r =
        compare_files
          ~reference_path:(reference_dir ^ "/" ^ file)
          ~candidate_path:(candidate_dir ^ "/" ^ file)
          ~name:file
      in
      if r.match_ then incr n_match else incr n_diverge ;
      print_result r ) ;
  if not (List.is_empty ref_only) then (
    printf "\n  Reference-only files:\n" ;
    List.iter ref_only ~f:(fun f -> printf "    %s\n" f) ) ;
  if not (List.is_empty cand_only) then (
    printf "\n  Candidate-only files:\n" ;
    List.iter cand_only ~f:(fun f -> printf "    %s\n" f) ) ;
  printf "\nSummary: %d exact matches, %d divergences, %d unmatched\n" !n_match
    !n_diverge
    (List.length ref_only + List.length cand_only)
