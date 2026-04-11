(** OCaml bindings to the Rust pairing-utils static library.

    Provides native computation of aux_witness (c, shift_power) from a
    Miller loop output, and alpha*beta pairing from VK points.

    Field elements are marshalled as pipe-delimited decimal strings. *)

open Core_kernel
module BI = Bignum_bigint

(** Raw FFI: compute_aux_witness.
    Input: pipe-delimited string of 12 fields (Fp12).
    Output: pipe-delimited string: "shift_power|g00|g01|...|h21" (13 fields). *)
external compute_aux_witness_raw : string -> string
  = "caml_pairing_utils_compute_aux_witness"

(** Raw FFI: make_alpha_beta.
    Input: pipe-delimited string of 6 fields (alpha/beta coords).
    Output: pipe-delimited string of 12 fields (Fp12). *)
external make_alpha_beta_raw : string -> string
  = "caml_pairing_utils_make_alpha_beta"

(** Convert an Fp12 constant to a pipe-delimited string.
    Order: g00|g01|g10|g11|g20|g21|h00|h01|h10|h11|h20|h21 *)
let fp12_to_pipe (((g0, g1, g2), (h0, h1, h2)) : Fp12.Constant.t) : string =
  let s (a, b) = BI.to_string a ^ "|" ^ BI.to_string b in
  String.concat ~sep:"|" [ s g0; s g1; s g2; s h0; s h1; s h2 ]

(** Parse a pipe-delimited string of 12 fields into an Fp12 constant. *)
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

(** Compute auxiliary witness from a Miller loop output (Fp12).
    Returns { c : Fp12.Constant.t ; shift_power : int }. *)
let compute_aux_witness (mlo : Fp12.Constant.t) : Proof_json.aux_witness =
  let input = fp12_to_pipe mlo in
  let result = compute_aux_witness_raw input in
  let parts = String.split result ~on:'|' in
  match parts with
  | shift_str :: rest ->
      let shift_power = Int.of_string shift_str in
      let c = pipe_to_fp12 (String.concat ~sep:"|" rest) in
      { Proof_json.c; shift_power }
  | [] ->
      failwith "compute_aux_witness: empty result"

(** Compute alpha*beta pairing from VK G1/G2 points.
    Returns Fp12 element = multi_miller_loop([alpha], [beta]). *)
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
  pipe_to_fp12 (make_alpha_beta_raw input)
