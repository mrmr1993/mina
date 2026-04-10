(** Parse SP1 PLONK proof from JSON fixture into accumulator constants.

    Deserializes the ABI-encoded hex proof, extracts public inputs,
    and constructs the initial Plonk_accumulator.t_const.

    Reference: nori-proof-conversion/src/plonk/proof.ts *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** Convert a bigint to Field3.Constant.t (which is just Bignum_bigint.t). *)
let bigint_to_field3 (v : Bignum_bigint.t) : FF.Field3.Constant.t = v

(** Decode a hex string (with 0x prefix) into bytes. *)
let hex_to_bytes (hex : string) : string =
  let hex = String.chop_prefix_exn hex ~prefix:"0x" in
  let len = String.length hex / 2 in
  String.init len ~f:(fun i ->
      Char.of_int_exn
        (Int.of_string ("0x" ^ String.sub hex ~pos:(i * 2) ~len:2)) )

(** ABI-decode the SP1 hex proof into 27 uint256 bigints.
    Matching nori: skip first 4 bytes (selector), decode as uint256[27]. *)
let abi_decode_proof (hex_proof : string) : Bignum_bigint.t array =
  (* Skip 0x prefix + first 8 hex chars (4 bytes = selector) *)
  let hex = String.chop_prefix_exn hex_proof ~prefix:"0x" in
  let shifted = String.drop_prefix hex 8 in
  (* Each uint256 is 32 bytes = 64 hex chars *)
  Array.init 27 ~f:(fun i ->
      let chunk = String.sub shifted ~pos:(i * 64) ~len:64 in
      Bignum_bigint.of_string ("0x" ^ chunk) )

(** Parse public inputs from programVk and piHex.
    Matching nori: nori-proof-conversion/src/plonk/parse_pi.ts *)
let parse_public_inputs ~(program_vk : string) ~(pi_hex : string) :
    FF.Field3.Constant.t * FF.Field3.Constant.t =
  (* pi0 = programVk as FrC *)
  let pi0 = bigint_to_field3 (Bignum_bigint.of_string program_vk) in
  (* pi1 = SHA256(piHex bytes) masked to 253 bits *)
  let pi_bytes = hex_to_bytes pi_hex in
  let digest = Digestif.SHA256.(digest_string pi_bytes |> to_raw_string) in
  let digest_bigint =
    String.foldi digest ~init:Bignum_bigint.zero ~f:(fun i acc c ->
        let shift = 31 - i in
        Bignum_bigint.(
          acc + (of_int (Char.to_int c) * pow (of_int 256) (of_int shift))) )
  in
  (* Mask to 253 bits: clear top 3 bits *)
  let mask_253 = Bignum_bigint.(pow (of_int 2) (of_int 253) - one) in
  let pi1_bigint = Bignum_bigint.(bit_and digest_bigint mask_253) in
  let pi1 = bigint_to_field3 pi1_bigint in
  (pi0, pi1)

(** Load and parse the SP1 PLONK proof fixture.
    Returns the initial Plonk_accumulator.t_const with proof fields
    populated and state containing pi0/pi1. *)
let load_fixture (path : string) : Plonk_accumulator.t_const =
  let json = Yojson.Safe.from_file path in
  let hex_proof = Yojson.Safe.Util.(member "hexProof" json |> to_string) in
  let program_vk = Yojson.Safe.Util.(member "programVk" json |> to_string) in
  let pi_hex = Yojson.Safe.Util.(member "piHex" json |> to_string) in
  (* Decode proof *)
  let vals = abi_decode_proof hex_proof in
  let f3 i = bigint_to_field3 vals.(i) in
  let proof : Plonk_accumulator.proof_const =
    { l_com_x = f3 0
    ; l_com_y = f3 1
    ; r_com_x = f3 2
    ; r_com_y = f3 3
    ; o_com_x = f3 4
    ; o_com_y = f3 5
    ; h0_x = f3 6
    ; h0_y = f3 7
    ; h1_x = f3 8
    ; h1_y = f3 9
    ; h2_x = f3 10
    ; h2_y = f3 11
    ; l_at_zeta = f3 12
    ; r_at_zeta = f3 13
    ; o_at_zeta = f3 14
    ; s1_at_zeta = f3 15
    ; s2_at_zeta = f3 16
    ; grand_product_x = f3 17
    ; grand_product_y = f3 18
    ; grand_product_at_omega_zeta = f3 19
    ; batch_opening_at_zeta_x = f3 20
    ; batch_opening_at_zeta_y = f3 21
    ; batch_opening_at_zeta_omega_x = f3 22
    ; batch_opening_at_zeta_omega_y = f3 23
    ; qcp_0_at_zeta = f3 24
    ; qcp_0_wire_x = f3 25
    ; qcp_0_wire_y = f3 26
    }
  in
  (* Parse public inputs *)
  let pi0, pi1 = parse_public_inputs ~program_vk ~pi_hex in
  (* Construct initial accumulator: proof populated, fs/state zero except pi0/pi1 *)
  let z3 = FF.Field3.Constant.zero in
  let z32 = Array.create ~len:32 Step.Field.Constant.zero in
  let z8 = Array.create ~len:8 Step.Field.Constant.zero in
  let fs : Plonk_accumulator.fs_const =
    { gamma_digest = z32
    ; gamma = z3
    ; beta_digest = z32
    ; beta = z3
    ; alpha_digest = z32
    ; alpha = z3
    ; zeta_digest = z32
    ; zeta = z3
    ; gamma_kzg_digest = z32
    ; gamma_kzg = z3
    }
  in
  let state : Plonk_accumulator.state_const =
    { pi0
    ; pi1
    ; zeta_pow_n = z3
    ; zh_eval = z3
    ; alpha_2_l0 = z3
    ; hx = z3
    ; hy = z3
    ; pi = z3
    ; linearized_opening = z3
    ; lcm_x = z3
    ; lcm_y = z3
    ; cm_x = z3
    ; cm_y = z3
    ; cm_opening = z3
    ; kzg_random = z3
    ; kzg_cm_x = z3
    ; kzg_cm_y = z3
    ; neg_fq_x = z3
    ; neg_fq_y = z3
    ; h_state = z8
    }
  in
  { proof; fs; state }
