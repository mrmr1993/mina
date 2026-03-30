(** Circuit witness helpers — provides per-circuit witness accessors.

    Each function calls [Circuit_config.get_tracker ()] internally,
    so they are safe to use inside [exists ~compute] closures. *)

module WT = Witness_tracker

(** Get the initial Fp12 accumulator for an ate loop circuit (zkp0-5).
    This is the f value at the start of the circuit's iteration range. *)
let get_ate_initial_f ~(circuit_index : int) : WT.Fp12.t =
  let tracker = Circuit_config.get_tracker () in
  let ate_ranges =
    [| (1, 13); (13, 24); (24, 35); (35, 47); (47, 59); (59, 65) |]
  in
  let begin_idx, _ = ate_ranges.(circuit_index) in
  if begin_idx <= 1 then WT.Fp12.one
  else WT.get_f_at_iteration tracker (begin_idx - 2)
