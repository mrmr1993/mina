(** SP1 PLONK proof and verification key structures.

    The PLONK proof contains polynomial commitments (G1 points)
    and evaluation values (Fr scalars) that the verifier checks
    via the PIOP and KZG pairing arguments. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field

(** Parsed PLONK proof (27 uint256 values decoded from ABI encoding). *)
type proof =
  { (* Wire commitments *)
    l_com : G1.Constant.t
  ; r_com : G1.Constant.t
  ; o_com : G1.Constant.t
  ; (* Quotient polynomial commitments *)
    h0 : G1.Constant.t
  ; h1 : G1.Constant.t
  ; h2 : G1.Constant.t
  ; (* Evaluation values at zeta *)
    l_at_zeta : FF.Bignum_bigint.t
  ; r_at_zeta : FF.Bignum_bigint.t
  ; o_at_zeta : FF.Bignum_bigint.t
  ; s1_at_zeta : FF.Bignum_bigint.t
  ; s2_at_zeta : FF.Bignum_bigint.t
  ; (* Grand product *)
    grand_product : G1.Constant.t
  ; grand_product_at_omega_zeta : FF.Bignum_bigint.t
  ; (* Opening proofs *)
    batch_opening_at_zeta : G1.Constant.t
  ; batch_opening_at_zeta_omega : G1.Constant.t
  ; (* Custom gate *)
    qcp_0_at_zeta : FF.Bignum_bigint.t
  ; qcp_0_wire : G1.Constant.t
  }

(** PLONK verification key (selector polynomial commitments). *)
type vk =
  { domain_size : int
  ; omega : FF.Bignum_bigint.t  (** Primitive root of unity *)
  ; (* Selector commitments *)
    ql : G1.Constant.t
  ; qr : G1.Constant.t
  ; qm : G1.Constant.t
  ; qo : G1.Constant.t
  ; qk : G1.Constant.t
  ; (* Permutation commitments *)
    s1 : G1.Constant.t
  ; s2 : G1.Constant.t
  ; s3 : G1.Constant.t
  ; (* Custom gate selector *)
    qcp_0 : G1.Constant.t option
  }

(** Parse a PLONK proof from JSON.
    The proof is encoded as an array of 27 uint256 values. *)
let parse_proof (j : Yojson.Safe.t) : proof =
  let open Yojson.Safe.Util in
  let g1 key =
    let x = member (key ^ "_x") j |> to_string |> FF.Bignum_bigint.of_string in
    let y = member (key ^ "_y") j |> to_string |> FF.Bignum_bigint.of_string in
    { G1.Constant.x; y }
  in
  let fr key = member key j |> to_string |> FF.Bignum_bigint.of_string in
  { l_com = g1 "l_com"
  ; r_com = g1 "r_com"
  ; o_com = g1 "o_com"
  ; h0 = g1 "h0"
  ; h1 = g1 "h1"
  ; h2 = g1 "h2"
  ; l_at_zeta = fr "l_at_zeta"
  ; r_at_zeta = fr "r_at_zeta"
  ; o_at_zeta = fr "o_at_zeta"
  ; s1_at_zeta = fr "s1_at_zeta"
  ; s2_at_zeta = fr "s2_at_zeta"
  ; grand_product = g1 "grand_product"
  ; grand_product_at_omega_zeta = fr "grand_product_at_omega_zeta"
  ; batch_opening_at_zeta = g1 "batch_opening_at_zeta"
  ; batch_opening_at_zeta_omega = g1 "batch_opening_at_zeta_omega"
  ; qcp_0_at_zeta = fr "qcp_0_at_zeta"
  ; qcp_0_wire = g1 "qcp_0_wire"
  }
