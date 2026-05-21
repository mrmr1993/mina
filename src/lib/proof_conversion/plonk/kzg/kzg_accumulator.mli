(** [KzgAccumulator]: the in-circuit accumulator for zkp12-23.

    After zkp12 transitions from the PLONK [Accumulator], circuits
    zkp13-23 operate on this KZG-specific accumulator. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** ATE_LOOP_COUNT for the BN254 pairing (length 65). *)
val ate_loop_count : int array

val ate_loop_len : int

(** Precomputed [ArrayListHasher.empty()] constant. *)
val array_list_hasher_empty : Step.Field.t

(** KZG proof: pairing points + shift + c values. *)
type kzg_proof =
  { a_x : FF.FpA.t
  ; a_y : FF.FpA.t
  ; neg_b_x : FF.FpA.t
  ; neg_b_y : FF.FpA.t
  ; shift_power : Step.Field.t
  ; c : Fp12.Circuit.t
  ; c_inv : Fp12.Circuit.t
  ; pi0 : FF.FpA.t
  ; pi1 : FF.FpA.t
  }

(** KZG state: f accumulator + lines-hash digest. *)
type kzg_state =
  { mutable f : Fp12.Circuit.t; mutable lines_hashes_digest : Step.Field.t }

type t = { proof : kzg_proof; state : kzg_state }

(** Build the chunked Random_oracle input for the accumulator. *)
val to_input : t -> Step.Field.t Random_oracle_input.Chunked.t

(** Hash with Poseidon, matching [hashPacked(KzgAccumulator, acc)]. *)
val hash_packed : t -> Step.Field.t

type kzg_proof_const =
  { a_x : FF.Field3.Constant.t
  ; a_y : FF.Field3.Constant.t
  ; neg_b_x : FF.Field3.Constant.t
  ; neg_b_y : FF.Field3.Constant.t
  ; shift_power : Step.Field.Constant.t
  ; c : Fp12.Constant.t
  ; c_inv : Fp12.Constant.t
  ; pi0 : FF.Field3.Constant.t
  ; pi1 : FF.Field3.Constant.t
  }

type kzg_state_const =
  { f : Fp12.Constant.t; lines_hashes_digest : Step.Field.Constant.t }

type t_const = { proof : kzg_proof_const; state : kzg_state_const }

val default_const : t_const

(** [Typ.t] for [KzgAccumulator] with the proper range checks. *)
val typ : (t, t_const) Step.Typ.t

(** Inject a constant KZG accumulator as circuit variables. *)
val of_constant : t_const -> t

(** Witness a [KzgAccumulator] using {!typ}. *)
val witness : unit -> t

(** String-leaved, named mirror of {!t_const} for transfer across a process
    boundary. Every leaf is a decimal string; the [Fp12] components are
    flattened to 12-element arrays of component strings. The field layout
    mirrors {!t_const}. *)
module Wire : sig
  type proof =
    { a_x : string
    ; a_y : string
    ; neg_b_x : string
    ; neg_b_y : string
    ; shift_power : string
    ; c : string array
    ; c_inv : string array
    ; pi0 : string
    ; pi1 : string
    }

  type state = { f : string array; lines_hashes_digest : string }

  type t = { proof : proof; state : state }

  (** JSON encoding of the wire form. *)
  val to_json : t -> Yojson.Safe.t

  (** Decode the wire form from JSON. *)
  val of_json : Yojson.Safe.t -> t
end

(** Reduce a KZG accumulator constant to its {!Wire.t} form. *)
val to_wire : t_const -> Wire.t

(** Reconstruct a KZG accumulator constant from its {!Wire.t} form. *)
val of_wire : Wire.t -> t_const
