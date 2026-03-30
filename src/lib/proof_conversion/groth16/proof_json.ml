(** Parse Groth16 proof and verification key from JSON.

    Handles RISC Zero proof format with G1 points as {x, y} and
    G2 points as {x_c0, x_c1, y_c0, y_c1}. *)

module BI = Bignum_bigint

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
  { x = bignum_of_json (member "x" j)
  ; y = bignum_of_json (member "y" j)
  }

(** Parse a G2 point from JSON {x_c0, x_c1, y_c0, y_c1}. *)
let g2_of_json (j : Yojson.Safe.t) : G2.Constant.t =
  let open Yojson.Safe.Util in
  { x =
      ( bignum_of_json (member "x_c0" j)
      , bignum_of_json (member "x_c1" j) )
  ; y =
      ( bignum_of_json (member "y_c0" j)
      , bignum_of_json (member "y_c1" j) )
  }

(** Parsed Groth16 verification key. *)
type vk =
  { alpha : G1.Constant.t
  ; beta : G2.Constant.t
  ; gamma : G2.Constant.t
  ; delta : G2.Constant.t
  ; ic : G1.Constant.t array
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
      let key = Printf.sprintf "ic%d" i in
      match Yojson.Safe.Util.member key j with
      | `Null ->
          Array.of_list (List.rev acc)
      | pt ->
          collect (i + 1) (g1_of_json pt :: acc)
    in
    collect 0 []
  in
  { alpha; beta; gamma; delta; ic }

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
      let key = Printf.sprintf "pi%d" i in
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
