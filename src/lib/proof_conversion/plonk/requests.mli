(** Request types for PLONK proof-conversion circuit private inputs.

    Each circuit witnesses its private inputs through the snarky request
    mechanism; the prover supplies values via {!handler}. *)

open Snarky_backendless.Request
open Proof_conversion_bn254
module Step = Pickles.Impls.Step

type _ t += Accumulator : Accumulator.t_const t

type _ t += Kzg_accumulator : Kzg_accumulator.t_const t

type _ t += Shift_power : Step.Field.Constant.t t

type _ t += C_fp12 : Fp12.Constant.t t

type _ t += G_chunk : Fp12.Constant.t array t

type _ t += Lines_hashes : Step.Field.Constant.t array t

type _ t += Flat_hashes : Step.Field.Constant.t array t

type _ t += Lhs_hashes : Step.Field.Constant.t array t

(** Witness values for a single circuit invocation. *)
type witness =
  { plonk_acc : Accumulator.t_const option
  ; kzg_acc : Kzg_accumulator.t_const option
  ; shift_power : Step.Field.Constant.t option
  ; c_fp12 : Fp12.Constant.t option
  ; g_chunk : Fp12.Constant.t array option
  ; lines_hashes : Step.Field.Constant.t array option
  ; flat_hashes : Step.Field.Constant.t array option
  ; lhs_hashes : Step.Field.Constant.t array option
  }

val empty_witness : witness

(** Create a request handler from witness values. *)
val handler :
     witness
  -> Snarky_backendless.Request.request
  -> Snarky_backendless.Request.response
