(** Parse Groth16 proof and verification key from JSON.

    Handles the RISC Zero proof format with G1 points as [{x, y}] and
    G2 points as [{x_c0, x_c1, y_c0, y_c1}]. *)

open Proof_conversion_bn254

(** Constant types re-exported for witness-tracker access. *)
module G1_constant = G1.Constant

module G2_constant = G2.Constant

(** Parse a bignum from a JSON string or int. *)
val bignum_of_json : Yojson.Safe.t -> Bignum_bigint.t

val g1_of_json : Yojson.Safe.t -> G1.Constant.t

val g2_of_json : Yojson.Safe.t -> G2.Constant.t

val fp2_of_json_fields :
  c0:Bignum_bigint.t -> c1:Bignum_bigint.t -> Fp2.Constant.t

val fp12_of_json : Yojson.Safe.t -> Fp12.Constant.t

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

val vk_of_json : Yojson.Safe.t -> vk

val fp12_to_json : Fp12.Constant.t -> Yojson.Safe.t

(** Auxiliary witness data [(c, shift_power)] computed externally. *)
type aux_witness = { c : Fp12.Constant.t; shift_power : int }

val aux_witness_of_json : Yojson.Safe.t -> aux_witness

val load_aux_witness : string -> aux_witness

(** Save auxiliary witness to JSON in nori-compatible format. *)
val save_aux_witness : string -> aux_witness -> unit

(** Parsed Groth16 proof. *)
type proof =
  { neg_a : G1.Constant.t
  ; b : G2.Constant.t
  ; c : G1.Constant.t
  ; public_inputs : Bignum_bigint.t array
  }

val proof_of_json : Yojson.Safe.t -> proof

val load_vk : string -> vk

val load_proof : string -> proof
