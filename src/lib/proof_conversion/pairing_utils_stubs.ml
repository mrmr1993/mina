(** OCaml bindings to the Rust pairing-utils static library.

    Provides native computation of aux_witness (c, shift_power) from a
    Miller loop output, and alpha*beta pairing from VK points. *)

open Core_kernel
module BI = Bignum_bigint

(** Raw FFI: compute_aux_witness.
    Input: list of 12 decimal strings (Fp12 as g00..h21).
    Output: (shift_power, list of 12 decimal strings for c). *)
external compute_aux_witness_raw : string list -> int * string list
  = "caml_pairing_utils_compute_aux_witness"

(** Raw FFI: make_alpha_beta.
    Input: list of 6 decimal strings (alpha_x, alpha_y, beta coords).
    Output: list of 12 decimal strings (Fp12 result). *)
external make_alpha_beta_raw : string list -> string list
  = "caml_pairing_utils_make_alpha_beta"

(** Convert an Fp12 constant (nested Fp6 * Fp6 tuples) to 12 decimal strings.
    Order: g00, g01, g10, g11, g20, g21, h00, h01, h10, h11, h20, h21 *)
let fp12_to_strings (((g0, g1, g2), (h0, h1, h2)) : Fp12.Constant.t) :
    string list =
  let bi_s (a, b) = [ BI.to_string a; BI.to_string b ] in
  List.concat [ bi_s g0; bi_s g1; bi_s g2; bi_s h0; bi_s h1; bi_s h2 ]

(** Convert 12 decimal strings back to an Fp12 constant. *)
let strings_to_fp12 (ss : string list) : Fp12.Constant.t =
  match ss with
  | [ g00; g01; g10; g11; g20; g21; h00; h01; h10; h11; h20; h21 ] ->
      let bi = BI.of_string in
      ( ((bi g00, bi g01), (bi g10, bi g11), (bi g20, bi g21))
      , ((bi h00, bi h01), (bi h10, bi h11), (bi h20, bi h21)) )
  | _ ->
      failwith
        (sprintf "strings_to_fp12: expected 12 strings, got %d" (List.length ss))

(** Compute auxiliary witness from a Miller loop output (Fp12).
    Returns { c : Fp12.Constant.t ; shift_power : int }. *)
let compute_aux_witness (mlo : Fp12.Constant.t) : Proof_json.aux_witness =
  let strings = fp12_to_strings mlo in
  let shift_power, c_strings = compute_aux_witness_raw strings in
  let c = strings_to_fp12 c_strings in
  { Proof_json.c; shift_power }

(** Compute alpha*beta pairing from VK G1/G2 points.
    Returns Fp12 element = multi_miller_loop([alpha], [beta]). *)
let make_alpha_beta ~(alpha_x : BI.t) ~(alpha_y : BI.t) ~(beta_x_c0 : BI.t)
    ~(beta_x_c1 : BI.t) ~(beta_y_c0 : BI.t) ~(beta_y_c1 : BI.t) :
    Fp12.Constant.t =
  let strings =
    make_alpha_beta_raw
      [ BI.to_string alpha_x
      ; BI.to_string alpha_y
      ; BI.to_string beta_x_c0
      ; BI.to_string beta_x_c1
      ; BI.to_string beta_y_c0
      ; BI.to_string beta_y_c1
      ]
  in
  strings_to_fp12 strings
