(** High-level wrappers around the Rust pairing-utils FFI.

    Converts between proof_conversion types and the pipe-delimited
    string format used by the raw FFI in proof_conversion_pairing_utils. *)

open Core_kernel
open Proof_conversion_groth16
open Proof_conversion_bn254
module BI = Bignum_bigint
module Raw = Proof_conversion_pairing_utils.Pairing_utils_stubs

let fp12_to_pipe (((g0, g1, g2), (h0, h1, h2)) : Fp12.Constant.t) : string =
  let s (a, b) = BI.to_string a ^ "|" ^ BI.to_string b in
  String.concat ~sep:"|" [ s g0; s g1; s g2; s h0; s h1; s h2 ]

let pipe_to_fp12 (s : string) : Fp12.Constant.t =
  let parts = String.split s ~on:'|' in
  match parts with
  | [ g00; g01; g10; g11; g20; g21; h00; h01; h10; h11; h20; h21 ] ->
      let bi = BI.of_string in
      ( ((bi g00, bi g01), (bi g10, bi g11), (bi g20, bi g21))
      , ((bi h00, bi h01), (bi h10, bi h11), (bi h20, bi h21)) )
  | _ ->
      failwith
        (sprintf "pipe_to_fp12: expected 12 fields, got %d" (List.length parts))

let parse_result result =
  let parts = String.split result ~on:'|' in
  match parts with
  | shift_str :: rest ->
      let shift_power = Int.of_string shift_str in
      let c = pipe_to_fp12 (String.concat ~sep:"|" rest) in
      { Proof_json.c; shift_power }
  | [] ->
      failwith "pairing_utils: empty FFI result"

(** Compute aux witness from a Miller loop output (Fp12). *)
let compute_aux_witness (mlo : Fp12.Constant.t) : Proof_json.aux_witness =
  parse_result (Raw.compute_aux_witness_raw (fp12_to_pipe mlo))

(** Compute Groth16 aux witness from proof/VK data.
    Runs the OCaml Miller loop to get the MLO (matching the circuit's
    convention), then calls Rust compute_aux_witness with the VK's w27. *)
let groth16_aux_witness ~(proof : Proof_json.proof) ~(vk : Proof_json.vk) :
    Proof_json.aux_witness =
  let mlo = Witness_tracker.compute_mlo ~proof ~vk in
  let input = fp12_to_pipe mlo ^ "|" ^ fp12_to_pipe vk.w27 in
  parse_result (Raw.groth16_aux_witness_with_w27_raw input)

(** Compute aux witness with a provided w27 (for use when MLO comes from
    OCaml rather than arkworks, to ensure consistent w27). *)
let compute_aux_witness_with_w27 (mlo : Fp12.Constant.t) (w27 : Fp12.Constant.t)
    : Proof_json.aux_witness =
  let input = fp12_to_pipe mlo ^ "|" ^ fp12_to_pipe w27 in
  parse_result (Raw.groth16_aux_witness_with_w27_raw input)

(** Compute alpha*beta pairing from VK G1/G2 points. *)
let make_alpha_beta ~(alpha_x : BI.t) ~(alpha_y : BI.t) ~(beta_x_c0 : BI.t)
    ~(beta_x_c1 : BI.t) ~(beta_y_c0 : BI.t) ~(beta_y_c1 : BI.t) :
    Fp12.Constant.t =
  let input =
    String.concat ~sep:"|"
      [ BI.to_string alpha_x
      ; BI.to_string alpha_y
      ; BI.to_string beta_x_c0
      ; BI.to_string beta_x_c1
      ; BI.to_string beta_y_c0
      ; BI.to_string beta_y_c1
      ]
  in
  pipe_to_fp12 (Raw.make_alpha_beta_raw input)

(** Compute KZG pairing MLO from A and -B G1 points.
    MLO = multi_miller_loop([A, -B], [g2, tau]) where g2/tau are fixed SRS. *)
let compute_kzg_mlo ~(a_x : BI.t) ~(a_y : BI.t) ~(neg_b_x : BI.t)
    ~(neg_b_y : BI.t) : Fp12.Constant.t =
  let input =
    String.concat ~sep:"|"
      [ BI.to_string a_x
      ; BI.to_string a_y
      ; BI.to_string neg_b_x
      ; BI.to_string neg_b_y
      ]
  in
  pipe_to_fp12 (Raw.compute_kzg_mlo_raw input)
