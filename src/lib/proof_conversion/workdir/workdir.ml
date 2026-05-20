(** Working directory management for staged proof conversion.

    Each stage reads/writes intermediate state to a working directory,
    enabling independent process execution and future parallelism. *)

open! Core_kernel
open Proof_conversion_plonk
open Proof_conversion_groth16
open Proof_conversion_bn254
module BI = Bignum_bigint
module Step = Pickles.Impls.Step

(** Recursive mkdir. *)
let mkdir_p dir =
  let rec go d =
    if not (Stdlib.Sys.file_exists d) then (
      go (Filename.dirname d) ;
      Stdlib.Sys.mkdir d 0o755 )
  in
  go dir

(** Proof system type for a working directory. *)
type system = Plonk of { base_count : int } | Groth16 of { base_count : int }

(* ---- Path helpers ---- *)

let state_dir w = Filename.concat w "state"

let proofs_dir w layer = Filename.concat w (sprintf "proofs/layer%d" layer)

let vks_dir w layer = Filename.concat w (sprintf "vks/layer%d" layer)

let meta_path w = Filename.concat w "meta.json"

let hash_path w n =
  Filename.concat (state_dir w)
    (if n < 0 then "hash_init.txt" else sprintf "hash_%d.txt" n)

let acc_path w n =
  Filename.concat (state_dir w)
    (if n < 0 then "acc_init.json" else sprintf "acc_%d.json" n)

let proof_path w ~layer ~index =
  Filename.concat (proofs_dir w layer) (sprintf "p%d.json" index)

let vk_path w ~layer ~index =
  Filename.concat (vks_dir w layer) (sprintf "v%d.json" index)

let node_vk_path w = Filename.concat w "vks/nodeVk.json"

(* ---- Serialization helpers ---- *)

let bi_to_json (x : BI.t) : Yojson.Safe.t = `String (BI.to_string x)

let bi_of_json (j : Yojson.Safe.t) : BI.t =
  BI.of_string (Yojson.Safe.Util.to_string j)

let fp2_to_json ((c0, c1) : Fp2.Constant.t) : Yojson.Safe.t =
  `List [ bi_to_json c0; bi_to_json c1 ]

let fp2_of_json (j : Yojson.Safe.t) : Fp2.Constant.t =
  match Yojson.Safe.Util.to_list j with
  | [ c0; c1 ] ->
      (bi_of_json c0, bi_of_json c1)
  | _ ->
      failwith "fp2_of_json: expected 2 elements"

let fp6_to_json ((c0, c1, c2) : Fp6.Constant.t) : Yojson.Safe.t =
  `List [ fp2_to_json c0; fp2_to_json c1; fp2_to_json c2 ]

let fp6_of_json (j : Yojson.Safe.t) : Fp6.Constant.t =
  match Yojson.Safe.Util.to_list j with
  | [ c0; c1; c2 ] ->
      (fp2_of_json c0, fp2_of_json c1, fp2_of_json c2)
  | _ ->
      failwith "fp6_of_json: expected 3 elements"

let fp12_to_json ((c0, c1) : Fp12.Constant.t) : Yojson.Safe.t =
  `List [ fp6_to_json c0; fp6_to_json c1 ]

let fp12_of_json (j : Yojson.Safe.t) : Fp12.Constant.t =
  match Yojson.Safe.Util.to_list j with
  | [ c0; c1 ] ->
      (fp6_of_json c0, fp6_of_json c1)
  | _ ->
      failwith "fp12_of_json: expected 2 elements"

let g1_to_json (p : G1.Constant.t) : Yojson.Safe.t =
  `Assoc [ ("x", bi_to_json p.x); ("y", bi_to_json p.y) ]

let g1_of_json (j : Yojson.Safe.t) : G1.Constant.t =
  let open Yojson.Safe.Util in
  { x = bi_of_json (member "x" j); y = bi_of_json (member "y" j) }

let g2_to_json (p : G2.Constant.t) : Yojson.Safe.t =
  `Assoc [ ("x", fp2_to_json p.x); ("y", fp2_to_json p.y) ]

let g2_of_json (j : Yojson.Safe.t) : G2.Constant.t =
  let open Yojson.Safe.Util in
  { x = fp2_of_json (member "x" j); y = fp2_of_json (member "y" j) }

let field_to_json (f : Step.Field.Constant.t) : Yojson.Safe.t =
  `String (Step.Field.Constant.to_string f)

let field_of_json (j : Yojson.Safe.t) : Step.Field.Constant.t =
  Step.Field.Constant.of_string (Yojson.Safe.Util.to_string j)

(* ---- Groth16 accumulator serialization ---- *)

module Groth16_ser = struct
  let proof_to_json (p : Accumulator.RecursionProof.Constant.t) : Yojson.Safe.t
      =
    `Assoc
      [ ("neg_a", g1_to_json p.neg_a)
      ; ("b", g2_to_json p.b)
      ; ("c", g1_to_json p.c)
      ; ("pi", g1_to_json p.pi)
      ; ("c_fp12", fp12_to_json p.c_fp12)
      ; ("c_inv", fp12_to_json p.c_inv)
      ; ("shift_power", `Int p.shift_power)
      ]

  let proof_of_json (j : Yojson.Safe.t) : Accumulator.RecursionProof.Constant.t
      =
    let open Yojson.Safe.Util in
    { neg_a = g1_of_json (member "neg_a" j)
    ; b = g2_of_json (member "b" j)
    ; c = g1_of_json (member "c" j)
    ; pi = g1_of_json (member "pi" j)
    ; c_fp12 = fp12_of_json (member "c_fp12" j)
    ; c_inv = fp12_of_json (member "c_inv" j)
    ; shift_power = to_int (member "shift_power" j)
    }

  let state_to_json (s : Accumulator.State.Constant.t) : Yojson.Safe.t =
    `Assoc
      [ ("t_point", g2_to_json s.t_point)
      ; ("f", fp12_to_json s.f)
      ; ("g_digest", field_to_json s.g_digest)
      ]

  let state_of_json (j : Yojson.Safe.t) : Accumulator.State.Constant.t =
    let open Yojson.Safe.Util in
    { t_point = g2_of_json (member "t_point" j)
    ; f = fp12_of_json (member "f" j)
    ; g_digest = field_of_json (member "g_digest" j)
    }

  let acc_to_json (acc : Accumulator.Constant.t) : Yojson.Safe.t =
    `Assoc
      [ ("proof", proof_to_json acc.proof); ("state", state_to_json acc.state) ]

  let acc_of_json (j : Yojson.Safe.t) : Accumulator.Constant.t =
    let open Yojson.Safe.Util in
    { proof = proof_of_json (member "proof" j)
    ; state = state_of_json (member "state" j)
    }

  (** Full Groth16 state includes accumulator + line_hashes + g_values. *)
  let full_state_to_json ~(acc : Accumulator.Constant.t)
      ~(line_hashes : Step.Field.Constant.t array)
      ~(g_values : Fp12.Constant.t array) : Yojson.Safe.t =
    `Assoc
      [ ("acc", acc_to_json acc)
      ; ( "line_hashes"
        , `List (Array.to_list (Array.map line_hashes ~f:field_to_json)) )
      ; ("g_values", `List (Array.to_list (Array.map g_values ~f:fp12_to_json)))
      ]

  let full_state_of_json (j : Yojson.Safe.t) :
      Accumulator.Constant.t
      * Step.Field.Constant.t array
      * Fp12.Constant.t array =
    let open Yojson.Safe.Util in
    let acc = acc_of_json (member "acc" j) in
    let line_hashes =
      member "line_hashes" j |> to_list |> List.to_array
      |> Array.map ~f:field_of_json
    in
    let g_values =
      member "g_values" j |> to_list |> List.to_array
      |> Array.map ~f:fp12_of_json
    in
    (acc, line_hashes, g_values)
end

(* ---- PLONK accumulator serialization ---- *)

(* ---- Generic Marshal-based serialization for complex types ---- *)

(** Write any OCaml value to a file using Marshal.
    Used for accumulator state where manual JSON serialization would be
    fragile. Safe for inter-process communication within the same binary. *)
let marshal_to_file ~path value =
  let oc = Out_channel.create path in
  Marshal.to_channel oc value [] ;
  Out_channel.close oc

(** Read a marshalled value from a file. *)
let marshal_from_file ~path =
  let ic = In_channel.create path in
  let v = Marshal.from_channel ic in
  In_channel.close ic ; v

(* ---- Accumulator state read/write ---- *)

(** Write Groth16 accumulator state as JSON. *)
let write_groth16_state ~workdir ~n ~(acc : Accumulator.Constant.t)
    ~(line_hashes : Step.Field.Constant.t array)
    ~(g_values : Fp12.Constant.t array) =
  let j = Groth16_ser.full_state_to_json ~acc ~line_hashes ~g_values in
  Yojson.Safe.to_file (acc_path workdir n) j

(** Read Groth16 accumulator state from JSON. *)
let read_groth16_state ~workdir ~n :
    Accumulator.Constant.t * Step.Field.Constant.t array * Fp12.Constant.t array
    =
  let j = Yojson.Safe.from_file (acc_path workdir n) in
  Groth16_ser.full_state_of_json j

(** Write PLONK accumulator state. *)
let write_plonk_state ~workdir ~n
    ~(acc : Proof_conversion_plonk.Accumulator.t_const) =
  marshal_to_file ~path:(acc_path workdir n)
    (Proof_conversion_plonk.Accumulator.to_wire acc)

(** Read PLONK accumulator state. *)
let read_plonk_state ~workdir ~n : Proof_conversion_plonk.Accumulator.t_const =
  Proof_conversion_plonk.Accumulator.of_wire
    ( marshal_from_file ~path:(acc_path workdir n)
      : Proof_conversion_plonk.Accumulator.Wire.t )

(** Write PLONK KZG accumulator state (for circuits 12+). *)
let write_plonk_kzg_state ~workdir ~n ~(kzg : Kzg_accumulator.t_const)
    ~(lines_hashes : Step.Field.Constant.t array)
    ~(g_values : Fp12.Constant.t array) =
  let j =
    `Assoc
      [ ( "lines_hashes"
        , `List (Array.to_list (Array.map lines_hashes ~f:field_to_json)) )
      ; ("g_values", `List (Array.to_list (Array.map g_values ~f:fp12_to_json)))
      ]
  in
  marshal_to_file ~path:(acc_path workdir n)
    (Kzg_accumulator.to_wire kzg, Yojson.Safe.to_string j)

(** Read PLONK KZG accumulator state. *)
let read_plonk_kzg_state ~workdir ~n :
    Kzg_accumulator.t_const
    * Step.Field.Constant.t array
    * Fp12.Constant.t array =
  let (kzg_wire, j_str) =
    ( marshal_from_file ~path:(acc_path workdir n)
      : Kzg_accumulator.Wire.t * string )
  in
  let kzg = Kzg_accumulator.of_wire kzg_wire in
  let j = Yojson.Safe.from_string j_str in
  let open Yojson.Safe.Util in
  let lines_hashes =
    member "lines_hashes" j |> to_list |> List.to_array
    |> Array.map ~f:field_of_json
  in
  let g_values =
    member "g_values" j |> to_list |> List.to_array |> Array.map ~f:fp12_of_json
  in
  (kzg, lines_hashes, g_values)

(* ---- Directory operations ---- *)

let max_layer = function Plonk _ -> 5 | Groth16 _ -> 4

let base_count = function
  | Plonk { base_count } ->
      base_count
  | Groth16 { base_count } ->
      base_count

(** Initialize a working directory for staged execution. *)
let init ~workdir ~(system : system) =
  let layers = max_layer system in
  mkdir_p (state_dir workdir) ;
  for i = 0 to layers do
    mkdir_p (proofs_dir workdir i) ;
    mkdir_p (vks_dir workdir i)
  done ;
  (* Write metadata *)
  let meta =
    match system with
    | Plonk { base_count } ->
        `Assoc [ ("system", `String "plonk"); ("base_count", `Int base_count) ]
    | Groth16 { base_count } ->
        `Assoc
          [ ("system", `String "groth16"); ("base_count", `Int base_count) ]
  in
  Yojson.Safe.to_file (meta_path workdir) meta

(** Detect the proof system from workdir metadata. *)
let detect_system ~workdir : system =
  let j = Yojson.Safe.from_file (meta_path workdir) in
  let open Yojson.Safe.Util in
  let sys = member "system" j |> to_string in
  let bc = member "base_count" j |> to_int in
  match sys with
  | "plonk" ->
      Plonk { base_count = bc }
  | "groth16" ->
      Groth16 { base_count = bc }
  | s ->
      failwith (sprintf "Unknown system: %s" s)

(* ---- Hash read/write ---- *)

let write_hash ~workdir ~n ~hash =
  Out_channel.write_all (hash_path workdir n)
    ~data:(Step.Field.Constant.to_string hash)

let read_hash ~workdir ~n =
  Step.Field.Constant.of_string
    (String.strip (In_channel.read_all (hash_path workdir n)))

(* ---- Proof read/write (base64) ---- *)

let write_proof_file ~path ~proof_base64 ~max_proofs_verified =
  let j =
    `Assoc
      [ ("proof", `String proof_base64)
      ; ("maxProofsVerified", `Int max_proofs_verified)
      ]
  in
  Yojson.Safe.to_file path j

let read_proof_file ~path =
  let j = Yojson.Safe.from_file path in
  let open Yojson.Safe.Util in
  (member "proof" j |> to_string, member "maxProofsVerified" j |> to_int)

(* ---- VK read/write (base64) ---- *)

let write_vk_file ~path ~vk_base64 ~vk_hash =
  let j = `Assoc [ ("data", `String vk_base64); ("hash", `String vk_hash) ] in
  Yojson.Safe.to_file path j

let read_vk_file ~path =
  let j = Yojson.Safe.from_file path in
  let open Yojson.Safe.Util in
  (member "data" j |> to_string, member "hash" j |> to_string)
