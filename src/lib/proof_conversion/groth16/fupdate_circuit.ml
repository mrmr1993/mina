(** f-update circuit body shared by zkp7-12.

    Each circuit performs cyclotomic squarings on f, multiplying in
    g values from the line accumulation and conditionally multiplying
    by c or c_inv based on the ate loop count bits. *)

open! Core_kernel
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Number of ate loop iterations processed per f-update circuit.
    zkp7 handles iterations 0-8, zkp8 handles 9-19, etc. *)
let iterations_per_circuit = [| 9; 11; 11; 11; 11; 12 |]

(** Starting g-value index for each f-update circuit. *)
let g_start_per_circuit = [| 0; 9; 20; 31; 42; 53 |]

let build ~(circuit_index : int) (input_hash : Step.Field.t) : Step.Field.t =
  assert (circuit_index >= 7 && circuit_index <= 12) ;
  let idx = circuit_index - 7 in
  let n_iters = iterations_per_circuit.(idx) in
  let g_start = g_start_per_circuit.(idx) in
  let ate = Bn254_params.ate_loop_count in
  (* f: the accumulated value entering this circuit.
     For zkp7, this is c_inv; for zkp8-12, it's the running state.f *)
  let f =
    Step.exists Fp12.Circuit.typ ~compute:(fun () ->
        let tracker = Circuit_config.get_tracker () in
        if circuit_index = 7 then WT.get_c_inv tracker else WT.get_f tracker )
  in
  let result = ref f in
  for i = 0 to n_iters - 1 do
    result := Fp12.cyclotomic_square !result ;
    (* Multiply by the g value for this iteration *)
    let g =
      Step.exists Fp12.Circuit.typ ~compute:(fun () ->
          let tracker = Circuit_config.get_tracker () in
          WT.get_g tracker (g_start + i) )
    in
    result := Fp12.mul !result g ;
    (* Conditional multiply by c_inv (bit=1) or c (bit=-1) *)
    let ate_idx = g_start + i in
    if ate_idx < Array.length ate then
      let bit = ate.(ate_idx) in
      if bit = 1 then
        let c_inv =
          Step.exists Fp12.Circuit.typ ~compute:(fun () ->
              let tracker = Circuit_config.get_tracker () in
              WT.get_c_inv tracker )
        in
        result := Fp12.mul !result c_inv
      else if bit = -1 then
        let c =
          Step.exists Fp12.Circuit.typ ~compute:(fun () ->
              let tracker = Circuit_config.get_tracker () in
              WT.get_c_fp12 tracker )
        in
        result := Fp12.mul !result c
  done ;
  ignore (!result : Fp12.Circuit.t) ;
  Accumulator_hash.combine_hashes
    [ input_hash; Step.Field.of_int circuit_index ]
