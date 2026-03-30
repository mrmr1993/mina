(** Gate sequence comparison between OCaml and nori circuit compilations.

    Compares gate JSON files dumped via [DUMP_PCS_GATES] on both sides.
    Each JSON file is a PCS dump: {"public_input_size": N, "gates": [...]}
    where each gate has "typ" (or "type"), "wires", and "coeffs".

    Can also handle nori's analyzeMethods format: {"gates": ["RangeCheck0", ...]}

    Usage:
      dune exec .../test_gate_comparison.exe -- \
        --reference /tmp/nori_gates --candidate /tmp/ocaml_gates *)

open! Core_kernel

(** Extract gate type from a gate object (supports both "typ" and "type"). *)
let gate_type_of_json (gate : Yojson.Safe.t) : string =
  match gate with
  | `Assoc fields ->
      let typ =
        match List.Assoc.find fields ~equal:String.equal "typ" with
        | Some (`String s) ->
            Some s
        | _ ->
            None
      in
      let typ =
        match typ with
        | Some _ ->
            typ
        | None -> (
            match List.Assoc.find fields ~equal:String.equal "type" with
            | Some (`String s) ->
                Some s
            | _ ->
                None )
      in
      Option.value_exn ~message:"gate object has no typ/type field" typ
  | `String s ->
      s (* nori compact format: plain string *)
  | _ ->
      failwith "unexpected gate format"

(** Extract gate types from a JSON file (auto-detects format). *)
let gate_types_of_file (path : string) : string list =
  let json = Yojson.Safe.from_file path in
  match json with
  | `Assoc fields -> (
      match List.Assoc.find fields ~equal:String.equal "gates" with
      | Some (`List gates) ->
          List.map gates ~f:gate_type_of_json
      | _ ->
          failwithf "no 'gates' array in %s" path () )
  | `List gates ->
      List.map gates ~f:gate_type_of_json
  | _ ->
      failwithf "unexpected top-level JSON in %s" path ()

(** Gate type -> count *)
let gate_summary (gates : string list) : (string * int) list =
  let counts = Hashtbl.create (module String) in
  List.iter gates ~f:(fun ty ->
      Hashtbl.update counts ty ~f:(function None -> 1 | Some n -> n + 1) ) ;
  Hashtbl.to_alist counts
  |> List.sort ~compare:(fun (a, _) (b, _) -> String.compare a b)

(** Find first divergence between two gate lists. *)
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

(** Compare two gate files and print results. *)
let compare_files ~reference_path ~candidate_path ~name =
  let ref_gates = gate_types_of_file reference_path in
  let cand_gates = gate_types_of_file candidate_path in
  let ref_summary = gate_summary ref_gates in
  let cand_summary = gate_summary cand_gates in
  let is_match = List.equal String.equal ref_gates cand_gates in
  let status = if is_match then "EXACT MATCH" else "DIVERGES" in
  printf "  %-30s %s  (ref=%d, cand=%d, delta=%+d)\n" name status
    (List.length ref_gates) (List.length cand_gates)
    (List.length cand_gates - List.length ref_gates) ;
  if not is_match then (
    ( match first_divergence ref_gates cand_gates with
    | Some (idx, ref_g, cand_g) ->
        let s = Option.value ~default:"<end>" in
        printf "    first divergence at gate %d: ref=%s, cand=%s\n" idx
          (s ref_g) (s cand_g)
    | None ->
        () ) ;
    (* Delta by type *)
    let all_types =
      List.dedup_and_sort ~compare:String.compare
        (List.map ref_summary ~f:fst @ List.map cand_summary ~f:fst)
    in
    let deltas =
      List.filter_map all_types ~f:(fun ty ->
          let r =
            List.Assoc.find ref_summary ~equal:String.equal ty
            |> Option.value ~default:0
          in
          let c =
            List.Assoc.find cand_summary ~equal:String.equal ty
            |> Option.value ~default:0
          in
          if c - r <> 0 then Some (ty, c - r) else None )
    in
    if not (List.is_empty deltas) then (
      printf "    delta by type:\n" ;
      List.iter deltas ~f:(fun (ty, d) -> printf "      %-20s %+d\n" ty d) ) ) ;
  is_match

(** List JSON files in a directory, sorted. *)
let list_json_files dir =
  Stdlib.Sys.readdir dir |> Array.to_list
  |> List.filter ~f:(String.is_suffix ~suffix:".json")
  |> List.sort ~compare:String.compare

(** Compare matching files between two directories. *)
let compare_dirs ~reference_dir ~candidate_dir =
  let ref_files = list_json_files reference_dir in
  let cand_files = list_json_files candidate_dir in
  printf "Gate Comparison\n" ;
  printf "  reference: %s (%d files)\n" reference_dir (List.length ref_files) ;
  printf "  candidate: %s (%d files)\n\n" candidate_dir (List.length cand_files) ;
  let ref_set = Set.of_list (module String) ref_files in
  let cand_set = Set.of_list (module String) cand_files in
  let common = Set.inter ref_set cand_set |> Set.to_list in
  let ref_only = Set.diff ref_set cand_set |> Set.to_list in
  let cand_only = Set.diff cand_set ref_set |> Set.to_list in
  let n_match = ref 0 in
  let n_diverge = ref 0 in
  List.iter common ~f:(fun file ->
      let ok =
        compare_files
          ~reference_path:(reference_dir ^ "/" ^ file)
          ~candidate_path:(candidate_dir ^ "/" ^ file)
          ~name:file
      in
      if ok then incr n_match else incr n_diverge ) ;
  if not (List.is_empty ref_only) then
    printf "\n  Reference-only: %s\n" (String.concat ~sep:", " ref_only) ;
  if not (List.is_empty cand_only) then
    printf "\n  Candidate-only: %s\n" (String.concat ~sep:", " cand_only) ;
  printf "\nSummary: %d match, %d diverge, %d unmatched\n" !n_match !n_diverge
    (List.length ref_only + List.length cand_only)
