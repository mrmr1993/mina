(** Request types for PLONK proof conversion circuit private inputs.

    Each circuit witnesses its private inputs via the snarky request
    mechanism. The prover supplies values through a handler that
    pattern-matches on these request constructors.

    Reference: nori-proof-conversion/src/plonk/recursion/prove_zkps.ts *)

open Snarky_backendless.Request
open Proof_conversion_bn254

module Step = Pickles.Impls.Step

(** Request for the PLONK accumulator (zkp0-11). *)
type _ t += Accumulator : Accumulator.t_const t

(** Request for the KZG accumulator (zkp12-23). *)
type _ t += Kzg_accumulator : Kzg_accumulator.t_const t

(** Request for the shift_power field element (zkp12). *)
type _ t += Shift_power : Step.Field.Constant.t t

(** Request for the Fp12 'c' value (zkp12). *)
type _ t += C_fp12 : Fp12.Constant.t t

(** Request for g_chunk Fp12 values (zkp17-23).
    The array length varies per circuit. *)
type _ t += G_chunk : Fp12.Constant.t array t

(** Request for lines_hashes field elements (zkp13-16).
    Array of ate_loop_len hashes. *)
type _ t += Lines_hashes : Step.Field.Constant.t array t

(** Request for flat_hashes field elements (zkp17-22).
    Array of (ate_loop_len - chunk_size) hashes. *)
type _ t += Flat_hashes : Step.Field.Constant.t array t

(** Request for lhs_hashes field elements (zkp23).
    Array of (ate_loop_len - 1) hashes. *)
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

let empty_witness : witness =
  { plonk_acc = None
  ; kzg_acc = None
  ; shift_power = None
  ; c_fp12 = None
  ; g_chunk = None
  ; lines_hashes = None
  ; flat_hashes = None
  ; lhs_hashes = None
  }

(** Create a request handler from witness values. *)
let handler (w : witness) :
    Snarky_backendless.Request.request -> Snarky_backendless.Request.response =
 fun (With { request; respond }) ->
  let k x = respond (Provide x) in
  match request with
  | Accumulator -> (
      match w.plonk_acc with Some v -> k v | None -> respond Unhandled )
  | Kzg_accumulator -> (
      match w.kzg_acc with Some v -> k v | None -> respond Unhandled )
  | Shift_power -> (
      match w.shift_power with Some v -> k v | None -> respond Unhandled )
  | C_fp12 -> (
      match w.c_fp12 with Some v -> k v | None -> respond Unhandled )
  | G_chunk -> (
      match w.g_chunk with Some v -> k v | None -> respond Unhandled )
  | Lines_hashes -> (
      match w.lines_hashes with Some v -> k v | None -> respond Unhandled )
  | Flat_hashes -> (
      match w.flat_hashes with Some v -> k v | None -> respond Unhandled )
  | Lhs_hashes -> (
      match w.lhs_hashes with Some v -> k v | None -> respond Unhandled )
  | _ ->
      respond Unhandled
