(** Precomputed verification-key constants for Groth16 circuits.

    Line coefficients are precomputed from the VK's delta and gamma G2
    points at circuit-definition time and embedded as circuit constants. *)

open Proof_conversion_bn254
module WT = Witness_tracker

type t =
  { delta_lines : WT.Line.t array
  ; gamma_lines : WT.Line.t array
  ; alpha_beta : Fp12.Circuit.t
  ; w27 : Fp12.Circuit.t
  ; w27_sq : Fp12.Circuit.t
  ; ic : G1.Circuit.t array
  }

(** Compute the flat line-coefficient array from a G2 point. *)
val compute_line_coeffs : WT.G2.t -> WT.Line.t array

(** Create VK constants from a parsed verification key. *)
val create : Proof_json.vk -> t
