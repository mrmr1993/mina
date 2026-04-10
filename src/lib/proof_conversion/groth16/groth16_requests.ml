(** Request types for Groth16 proof conversion circuit private inputs.

    Each circuit witnesses its private inputs via the snarky request
    mechanism. The prover supplies values through a handler that
    pattern-matches on these request constructors. *)

open Snarky_backendless.Request
module Step = Pickles.Impls.Step

(** Request for the Groth16 accumulator. *)
type _ t += Groth16_accumulator : Accumulator.Constant.t t

(** Request for line hashes (ate loop circuits 0-6). *)
type _ t += Line_hashes : Step.Field.Constant.t array t

(** Request for B-line coefficients (ate loop circuits 0-6). *)
type _ t += B_lines : (Fp2.Constant.t * Fp2.Constant.t) array t

(** Request for g_chunk Fp12 values (f-update circuits 7-12). *)
type _ t += G_chunk : Fp12.Constant.t array t

(** Request for lhs_hashes (f-update circuits 7-13). *)
type _ t += Lhs_hashes : Step.Field.Constant.t array t

(** Request for rhs_hashes (f-update circuits 7-12). *)
type _ t += Rhs_hashes : Step.Field.Constant.t array t

(** Request for final g value (circuit 13). *)
type _ t += Final_g : Fp12.Constant.t t

(** Request for public inputs pis[0..4] (circuits 14-15). *)
type _ t +=
  | Public_inputs : Snarky_foreign_field.Foreign_field.Field3.Constant.t array t

(** Request for PI point (circuit 15). *)
type _ t += Pi_point : G1.Constant.t t

(** Request for partial IC accumulation point (circuit 15). *)
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

let empty_witness : witness =
  { accumulator = None
  ; line_hashes = None
  ; b_lines = None
  ; g_chunk = None
  ; lhs_hashes = None
  ; rhs_hashes = None
  ; final_g = None
  ; public_inputs = None
  ; pi_point = None
  ; partial_ic_acc = None
  }

(** Create a request handler from witness values. *)
let handler (w : witness) :
    Snarky_backendless.Request.request -> Snarky_backendless.Request.response =
 fun (With { request; respond }) ->
  let k x = respond (Provide x) in
  match request with
  | Groth16_accumulator -> (
      match w.accumulator with Some v -> k v | None -> respond Unhandled )
  | Line_hashes -> (
      match w.line_hashes with Some v -> k v | None -> respond Unhandled )
  | B_lines -> (
      match w.b_lines with Some v -> k v | None -> respond Unhandled )
  | G_chunk -> (
      match w.g_chunk with Some v -> k v | None -> respond Unhandled )
  | Lhs_hashes -> (
      match w.lhs_hashes with Some v -> k v | None -> respond Unhandled )
  | Rhs_hashes -> (
      match w.rhs_hashes with Some v -> k v | None -> respond Unhandled )
  | Final_g -> (
      match w.final_g with Some v -> k v | None -> respond Unhandled )
  | Public_inputs -> (
      match w.public_inputs with Some v -> k v | None -> respond Unhandled )
  | Pi_point -> (
      match w.pi_point with Some v -> k v | None -> respond Unhandled )
  | Partial_ic_acc -> (
      match w.partial_ic_acc with Some v -> k v | None -> respond Unhandled )
  | _ ->
      respond Unhandled
