(** Parse Groth16 proof and verification key from JSON.

    Handles RISC Zero proof format with G1 points as {x, y} and
    G2 points as {x_c0, x_c1, y_c0, y_c1}. *)

open! Core_kernel
module BI = Bignum_bigint

(** Re-export constant types for witness_tracker access. *)
module G1_constant = G1.Constant

module G2_constant = G2.Constant

(** Parse a bignum from a JSON string value. *)
let bignum_of_json (j : Yojson.Safe.t) : Bignum_bigint.t =
  match j with
  | `String s ->
      BI.of_string s
  | `Int i ->
      BI.of_int i
  | _ ->
      failwith "bignum_of_json: expected string or int"

(** Parse a G1 point from JSON {x, y}. *)
let g1_of_json (j : Yojson.Safe.t) : G1.Constant.t =
  let open Yojson.Safe.Util in
  { x = bignum_of_json (member "x" j); y = bignum_of_json (member "y" j) }

(** Parse a G2 point from JSON {x_c0, x_c1, y_c0, y_c1}. *)
let g2_of_json (j : Yojson.Safe.t) : G2.Constant.t =
  let open Yojson.Safe.Util in
  { x = (bignum_of_json (member "x_c0" j), bignum_of_json (member "x_c1" j))
  ; y = (bignum_of_json (member "y_c0" j), bignum_of_json (member "y_c1" j))
  }

(** Parse an Fp2 constant from JSON {c0: "...", c1: "..."}
    or from two named fields. *)
let fp2_of_json_fields ~c0 ~c1 : Fp2.Constant.t = (c0, c1)

(** Parse an Fp12 constant from JSON with g00..g21, h00..h21 fields.
    Fp12 = (Fp6(Fp2, Fp2, Fp2), Fp6(Fp2, Fp2, Fp2))
    where g = c0 (Fp6) and h = c1 (Fp6). *)
let fp12_of_json (j : Yojson.Safe.t) : Fp12.Constant.t =
  let open Yojson.Safe.Util in
  let g f = bignum_of_json (member f j) in
  let c0 : Fp6.Constant.t =
    ( fp2_of_json_fields ~c0:(g "g00") ~c1:(g "g01")
    , fp2_of_json_fields ~c0:(g "g10") ~c1:(g "g11")
    , fp2_of_json_fields ~c0:(g "g20") ~c1:(g "g21") )
  in
  let c1 : Fp6.Constant.t =
    ( fp2_of_json_fields ~c0:(g "h00") ~c1:(g "h01")
    , fp2_of_json_fields ~c0:(g "h10") ~c1:(g "h11")
    , fp2_of_json_fields ~c0:(g "h20") ~c1:(g "h21") )
  in
  (c0, c1)

(** Parsed Groth16 verification key. *)
type vk =
  { alpha : G1.Constant.t
  ; beta : G2.Constant.t
  ; gamma : G2.Constant.t
  ; delta : G2.Constant.t
  ; ic : G1.Constant.t array
  ; alpha_beta : Fp12.Constant.t
  ; w27 : Fp12.Constant.t
  }

(** Parse a verification key from JSON. *)
let vk_of_json (j : Yojson.Safe.t) : vk =
  let open Yojson.Safe.Util in
  let alpha = g1_of_json (member "alpha" j) in
  let beta = g2_of_json (member "beta" j) in
  let gamma = g2_of_json (member "gamma" j) in
  let delta = g2_of_json (member "delta" j) in
  (* Collect IC points: ic0, ic1, ic2, ... *)
  let ic =
    let rec collect i acc =
      let key = sprintf "ic%d" i in
      match Yojson.Safe.Util.member key j with
      | `Null ->
          Array.of_list (List.rev acc)
      | pt ->
          collect (i + 1) (g1_of_json pt :: acc)
    in
    collect 0 []
  in
  let alpha_beta =
    match member "alpha_beta" j with
    | `Null ->
        (* Raw VK: alpha_beta must be computed externally *)
        (Fp6.Constant.zero, Fp6.Constant.zero)
    | ab_json ->
        fp12_of_json ab_json
  in
  let w27 = fp12_of_json (member "w27" j) in
  { alpha; beta; gamma; delta; ic; alpha_beta; w27 }

(** Serialize an Fp12 constant to JSON with g00..h21 field names. *)
let fp12_to_json ((c0, c1) : Fp12.Constant.t) : Yojson.Safe.t =
  let s x = `String (BI.to_string x) in
  let (g00, g01), (g10, g11), (g20, g21) = c0 in
  let (h00, h01), (h10, h11), (h20, h21) = c1 in
  `Assoc
    [ ("g00", s g00)
    ; ("g01", s g01)
    ; ("g10", s g10)
    ; ("g11", s g11)
    ; ("g20", s g20)
    ; ("g21", s g21)
    ; ("h00", s h00)
    ; ("h01", s h01)
    ; ("h10", s h10)
    ; ("h11", s h11)
    ; ("h20", s h20)
    ; ("h21", s h21)
    ]

(** Auxiliary witness data (c, shift_power) computed externally. *)
type aux_witness = { c : Fp12.Constant.t; shift_power : int }

(** Parse auxiliary witness from JSON. *)
let aux_witness_of_json (j : Yojson.Safe.t) : aux_witness =
  let open Yojson.Safe.Util in
  let c = fp12_of_json (member "c" j) in
  let shift_power =
    match member "shift_power" j with
    | `String s ->
        Int.of_string s
    | `Int i ->
        i
    | _ ->
        failwith "aux_witness: expected int for shift_power"
  in
  { c; shift_power }

(** Load and parse auxiliary witness from a JSON file. *)
let load_aux_witness (path : string) : aux_witness =
  let j = Yojson.Safe.from_file path in
  aux_witness_of_json j

(** Save auxiliary witness to JSON file in nori-compatible format. *)
let save_aux_witness (path : string) (aux : aux_witness) : unit =
  let j =
    `Assoc
      [ ("c", fp12_to_json aux.c)
      ; ("shift_power", `String (Int.to_string aux.shift_power))
      ]
  in
  Yojson.Safe.to_file path j

(** Parsed Groth16 proof. *)
type proof =
  { neg_a : G1.Constant.t
  ; b : G2.Constant.t
  ; c : G1.Constant.t
  ; public_inputs : Bignum_bigint.t array
  }

(** Parse a proof from JSON. *)
let proof_of_json (j : Yojson.Safe.t) : proof =
  let open Yojson.Safe.Util in
  let neg_a = g1_of_json (member "negA" j) in
  let b = g2_of_json (member "B" j) in
  let c = g1_of_json (member "C" j) in
  (* Collect public inputs: pi1, pi2, pi3, ... *)
  let public_inputs =
    let rec collect i acc =
      let key = sprintf "pi%d" i in
      match Yojson.Safe.Util.member key j with
      | `Null ->
          Array.of_list (List.rev acc)
      | v ->
          collect (i + 1) (bignum_of_json v :: acc)
    in
    collect 1 []
  in
  { neg_a; b; c; public_inputs }

(** Load and parse a VK from a JSON file. *)
let load_vk (path : string) : vk =
  let j = Yojson.Safe.from_file path in
  vk_of_json j

(** Load and parse a proof from a JSON file. *)
let load_proof (path : string) : proof =
  let j = Yojson.Safe.from_file path in
  proof_of_json j
