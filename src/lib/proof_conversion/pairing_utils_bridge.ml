(** High-level wrappers around the Rust pairing-utils FFI.

    Converts between proof_conversion types and the pipe-delimited
    string format used by the raw FFI in proof_conversion_pairing_utils. *)

open Core_kernel
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

(** Compute Groth16 aux witness from proof/VK points.
    Uses arkworks multi_miller_loop internally. *)
let groth16_aux_witness ~(proof : Proof_json.proof) ~(vk : Proof_json.vk) :
    Proof_json.aux_witness =
  let s = BI.to_string in
  let pi = Witness_tracker.compute_pi ~proof ~vk in
  let s2 (a, b) = s a ^ "|" ^ s b in
  let input =
    String.concat ~sep:"|"
      [ s proof.neg_a.x
      ; s proof.neg_a.y
      ; s2 proof.b.x
      ; s2 proof.b.y
      ; s proof.c.x
      ; s proof.c.y
      ; s pi.x
      ; s pi.y
      ; s2 vk.gamma.x
      ; s2 vk.gamma.y
      ; s2 vk.delta.x
      ; s2 vk.delta.y
      ; fp12_to_pipe vk.alpha_beta
      ]
  in
  parse_result (Raw.groth16_aux_witness_raw input)

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
