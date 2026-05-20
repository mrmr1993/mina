(** SP1 PLONK proof and verification-key structures. *)

open Proof_conversion_bn254
module FF = Snarky_foreign_field.Foreign_field

(** Parsed PLONK proof (27 uint256 values decoded from ABI encoding). *)
type proof =
  { l_com : G1.Constant.t
  ; r_com : G1.Constant.t
  ; o_com : G1.Constant.t
  ; h0 : G1.Constant.t
  ; h1 : G1.Constant.t
  ; h2 : G1.Constant.t
  ; l_at_zeta : FF.Bignum_bigint.t
  ; r_at_zeta : FF.Bignum_bigint.t
  ; o_at_zeta : FF.Bignum_bigint.t
  ; s1_at_zeta : FF.Bignum_bigint.t
  ; s2_at_zeta : FF.Bignum_bigint.t
  ; grand_product : G1.Constant.t
  ; grand_product_at_omega_zeta : FF.Bignum_bigint.t
  ; batch_opening_at_zeta : G1.Constant.t
  ; batch_opening_at_zeta_omega : G1.Constant.t
  ; qcp_0_at_zeta : FF.Bignum_bigint.t
  ; qcp_0_wire : G1.Constant.t
  }

(** PLONK verification key (selector polynomial commitments). *)
type vk =
  { domain_size : int
  ; domain_size_bits : int array
  ; inv_domain_size : FF.Bignum_bigint.t
  ; omega : FF.Bignum_bigint.t
  ; coset_shift : FF.Bignum_bigint.t
  ; g1_gen : G1.Constant.t
  ; ql : G1.Constant.t
  ; qr : G1.Constant.t
  ; qm : G1.Constant.t
  ; qo : G1.Constant.t
  ; qk : G1.Constant.t
  ; s1 : G1.Constant.t
  ; s2 : G1.Constant.t
  ; s3 : G1.Constant.t
  ; qcp_0 : G1.Constant.t option
  ; omega_pow_i : FF.Bignum_bigint.t
  ; omega_pow_i_div_n : FF.Bignum_bigint.t
  }

(** Parse a PLONK proof from JSON (27 uint256 values). *)
val parse_proof : Yojson.Safe.t -> proof
