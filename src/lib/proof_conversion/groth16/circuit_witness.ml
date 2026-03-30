(** Circuit witness configuration for Groth16 circuits.

    Provides access to the tracker's precomputed data and controls
    whether circuits use variable (real) or constant witnesses. *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Whether to use real (variable) witnesses from the tracker. *)
let use_variable_witnesses = true

(** Get the Fp12 accumulator for a specific circuit from the tracker. *)
let get_circuit_fp12 ~(circuit_index : int) : WT.Fp12.t =
  let tracker = Circuit_config.get_tracker () in
  let ate_ranges =
    [| (1, 13); (13, 24); (24, 35); (35, 47); (47, 59); (59, 65) |]
  in
  if circuit_index >= 0 && circuit_index <= 5 then
    let begin_idx, _ = ate_ranges.(circuit_index) in
    if begin_idx <= 1 then WT.Fp12.one
    else WT.get_f_at_iteration tracker (begin_idx - 2)
  else if circuit_index <= 12 then WT.get_f tracker
  else WT.Fp12.one
