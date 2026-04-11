(** Low-level OCaml bindings to the Rust pairing-utils static library.

    All functions use pipe-delimited decimal strings for field elements.
    Higher-level wrappers that convert to/from proof_conversion types
    live in the proof_conversion library (pairing_utils_bridge.ml). *)

(** Compute aux witness from Fp12 MLO.
    Input: pipe-delimited 12 fields (Fp12).
    Output: "shift_power|c_g00|c_g01|...|c_h21" (13 fields). *)
external compute_aux_witness_raw : string -> string
  = "caml_pairing_utils_compute_aux_witness"

(** Compute Groth16 aux witness from proof/VK points via arkworks MLO.
    Input: 42 pipe-delimited fields (negA, B, C, PI, gamma, delta, alpha_beta, w27).
    Output: "shift_power|c_g00|...|c_h21" (13 fields). *)
external groth16_aux_witness_raw : string -> string
  = "caml_pairing_utils_groth16_aux_witness"

(** Compute aux witness from MLO + w27 (both Fp12).
    Input: 24 pipe-delimited fields (MLO 12 + w27 12).
    Output: "shift_power|c_g00|...|c_h21" (13 fields). *)
external groth16_aux_witness_with_w27_raw : string -> string
  = "caml_pairing_utils_aux_witness_with_w27"

(** Compute alpha*beta pairing.
    Input: 6 pipe-delimited fields (alpha_x, alpha_y, beta coords).
    Output: 12 pipe-delimited fields (Fp12). *)
external make_alpha_beta_raw : string -> string
  = "caml_pairing_utils_make_alpha_beta"
