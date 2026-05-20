(** Parse an SP1 PLONK proof from a JSON fixture into accumulator
    constants. *)

open Proof_conversion_bn254
module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** Convert a bigint to a [Field3.Constant.t]. *)
val bigint_to_field3 : Bignum_bigint.t -> FF.Field3.Constant.t

(** Decode a [0x]-prefixed hex string into raw bytes. *)
val hex_to_bytes : string -> string

(** ABI-decode the SP1 hex proof into 27 uint256 bigints. *)
val abi_decode_proof : string -> Bignum_bigint.t array

(** Parse the [(pi0, pi1)] public inputs from [program_vk] and [pi_hex]. *)
val parse_public_inputs :
     program_vk:string
  -> pi_hex:string
  -> FF.Field3.Constant.t * FF.Field3.Constant.t

(** Load and parse the SP1 PLONK proof fixture. *)
val load_fixture : string -> Accumulator.t_const

(** Auxiliary witness data for zkp12. *)
type aux_witness =
  { shift_power : Step.Field.Constant.t; c_fp12 : Fp12.Constant.t }

val parse_aux_witness : Yojson.Safe.t -> aux_witness

(** Load a fixture and its aux witness. *)
val load_fixture_with_aux : string -> Accumulator.t_const * aux_witness

(** Parse the SP1 JSON format, returning [(hex_proof, program_vk, pi_hex)]. *)
val parse_sp1_json : Yojson.Safe.t -> string * string * string

(** Load from the SP1 JSON format (nori CLI input). *)
val load_sp1 : string -> Accumulator.t_const
