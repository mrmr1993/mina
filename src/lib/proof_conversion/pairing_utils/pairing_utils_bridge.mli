(** High-level wrappers around the Rust pairing-utils FFI.

    Converts between proof_conversion types and the pipe-delimited string
    format used by the raw FFI in [proof_conversion_pairing_utils]. The
    pipe-format plumbing is an implementation detail and is not exposed. *)

open Proof_conversion_groth16
open Proof_conversion_bn254

(** Compute the aux witness from a Miller-loop output (Fp12). *)
val compute_aux_witness : Fp12.Constant.t -> Proof_json.aux_witness

(** Compute the Groth16 aux witness from proof/VK data. Runs the OCaml
    Miller loop to obtain the MLO (matching the circuit's convention),
    then calls the Rust FFI with the VK's [w27]. *)
val groth16_aux_witness :
  proof:Proof_json.proof -> vk:Proof_json.vk -> Proof_json.aux_witness

(** Compute the aux witness with a caller-provided [w27] — used when the
    MLO comes from the OCaml Miller loop rather than arkworks, so the
    same [w27] is used on both sides. *)
val compute_aux_witness_with_w27 :
  Fp12.Constant.t -> Fp12.Constant.t -> Proof_json.aux_witness

(** Compute the alpha*beta pairing from the VK's G1/G2 coordinates. *)
val make_alpha_beta :
     alpha_x:Bignum_bigint.t
  -> alpha_y:Bignum_bigint.t
  -> beta_x_c0:Bignum_bigint.t
  -> beta_x_c1:Bignum_bigint.t
  -> beta_y_c0:Bignum_bigint.t
  -> beta_y_c1:Bignum_bigint.t
  -> Fp12.Constant.t

(** Compute the KZG pairing MLO from the A and -B G1 points:
    [multi_miller_loop([A; -B], [g2; tau])] with fixed SRS [g2]/[tau]. *)
val compute_kzg_mlo :
     a_x:Bignum_bigint.t
  -> a_y:Bignum_bigint.t
  -> neg_b_x:Bignum_bigint.t
  -> neg_b_y:Bignum_bigint.t
  -> Fp12.Constant.t
