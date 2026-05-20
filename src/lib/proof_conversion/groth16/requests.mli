(** Request types for Groth16 proof-conversion circuit private inputs.

    Each circuit witnesses its private inputs through the snarky request
    mechanism; the prover supplies values via {!handler}. *)

open Snarky_backendless.Request
open Proof_conversion_bn254
module Step = Pickles.Impls.Step

type _ t += Groth16_accumulator : Accumulator.Constant.t t

type _ t += Line_hashes : Step.Field.Constant.t array t

type _ t += B_lines : (Fp2.Constant.t * Fp2.Constant.t) array t

type _ t += G_chunk : Fp12.Constant.t array t

type _ t += Lhs_hashes : Step.Field.Constant.t array t

type _ t += Rhs_hashes : Step.Field.Constant.t array t

type _ t += Final_g : Fp12.Constant.t t

type _ t +=
  | Public_inputs : Snarky_foreign_field.Foreign_field.Field3.Constant.t array t

type _ t += Pi_point : G1.Constant.t t

type _ t += Partial_ic_acc : G1.Constant.t t

(** Witness values for a single Groth16 circuit invocation. *)
type witness =
  { accumulator : Accumulator.Constant.t option
  ; line_hashes : Step.Field.Constant.t array option
  ; b_lines : (Fp2.Constant.t * Fp2.Constant.t) array option
  ; g_chunk : Fp12.Constant.t array option
  ; lhs_hashes : Step.Field.Constant.t array option
  ; rhs_hashes : Step.Field.Constant.t array option
  ; final_g : Fp12.Constant.t option
  ; public_inputs :
      Snarky_foreign_field.Foreign_field.Field3.Constant.t array option
  ; pi_point : G1.Constant.t option
  ; partial_ic_acc : G1.Constant.t option
  }

val empty_witness : witness

(** Create a request handler from witness values. *)
val handler :
     witness
  -> Snarky_backendless.Request.request
  -> Snarky_backendless.Request.response
